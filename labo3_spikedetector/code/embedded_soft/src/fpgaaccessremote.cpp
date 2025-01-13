#include "fpgaaccessremote.hpp"

#include <iosfwd>

#include <iostream>
#include <sstream>
#include <stdio.h>
#include <string.h> //strlen
#include <stdlib.h> //strlen
#include <sys/socket.h>
#include <arpa/inet.h> //inet_addr
#include <unistd.h> //write

void *FPGAAccess::server()
{
	int socket_desc, client_sock, c;
	struct sockaddr_in server, client;

	//Create socket
	socket_desc = socket(AF_INET, SOCK_STREAM, 0);
	if (socket_desc == -1) {
		printf("Could not create socket");
	}
	puts("Socket created");

	//Prepare the sockaddr_in structure
	server.sin_family = AF_INET;
	server.sin_addr.s_addr = INADDR_ANY;
	server.sin_port = htons(8888);

	//Bind
	if (bind(socket_desc, (struct sockaddr *)&server, sizeof(server)) < 0) {
		//print the error message
		perror("bind failed. Error");
		return NULL;
	}
	puts("bind done");

	//Listen
	listen(socket_desc, 3);

	//Accept and incoming connection
	puts("Waiting for incoming connections...");
	c = sizeof(struct sockaddr_in);

	client_sock = accept(socket_desc, (struct sockaddr *)&client,
			     (socklen_t *)&c);

	if (client_sock <= 0) {
		perror("accept failed");
		return NULL;
	}

	puts("Connection accepted");

	sock = client_sock;

	receivedCondVar.notify_all();

	puts("Handler assigned");

	return NULL;
}

/*
 * This will handle connection for each client
 * */
void *FPGAAccess::connectionHandler(void *socket_desc)
{
	//Get the socket descriptor
	return nullptr;
}

FPGAAccess::FPGAAccess()
{
}

FPGAAccess::~FPGAAccess()
{
	if (sock != 0) {
		sendMessage("end_test\n");
		// Sleep to be sure that data are correctly send
		sleep(5);
		shutdown(sock, SHUT_RDWR);
	}

	if (fpgaServerThread.joinable())
		fpgaServerThread.join();

	if (receiverThread.joinable())
		receiverThread.join();
}

FPGAAccess &FPGAAccess::getInstance()
{
	static FPGAAccess access;
	return access;
}

void FPGAAccess::init()
{
	fpgaServerThread = std::thread(&FPGAAccess::server, this);
	receiverThread = std::thread(&FPGAAccess::receiver, this);
	waitConnection();
}

void FPGAAccess::waitConnection()
{
	std::unique_lock<std::mutex> lk(receiveMutex);

	receivedCondVar.wait(lk, [this] { return sock != 0; });
}

void FPGAAccess::receiver()
{
	char clientMessage[2000];
	char messageCommand[2000];
	int read_size;

	waitConnection();

	while ((read_size = recv(sock, clientMessage, 2000, 0)) > 0) {
		clientMessage[read_size] = '\0';

		std::stringstream stream(clientMessage);
		stream >> messageCommand;

		if (strcmp(messageCommand, "irq") == 0) {
			if (handler != nullptr) {
				std::string clientStr(clientMessage);
				handler(clientStr);
			} else {
				std::cout << "IRQ received, but no handler!"
					  << std::endl;
			}
		} else {
			// We got a response to a command, add it to the FIFO and inform responsible thread
			std::unique_lock<std::mutex> lk(receiveMutex);

			receivedFifo.push(clientMessage);
			receivedCondVar.notify_all();
		}
	}
}

std::string FPGAAccess::getData()
{
	std::string message;
	std::unique_lock<std::mutex> lk(receiveMutex);

	receivedCondVar.wait(lk, [this] { return !receivedFifo.empty(); });

	message = receivedFifo.front();
	receivedFifo.pop();

	return message;
}

void FPGAAccess::sendMessage(const std::string &message)
{
	write(sock, message.data(), strlen(message.data()));
}

void FPGAAccess::sendMessage(const char *message)
{
	write(sock, message, strlen(message));
}

void FPGAAccess::startAcquisition()
{
	sendMessage("wr 1 1\n");
}

void FPGAAccess::stopAcquisition()
{
	sendMessage("wr 1 0\n");
}

void FPGAAccess::setInterruptHandler(irq_handler_t handler)
{
	this->handler = handler;
}

uint16_t FPGAAccess::getStatus()
{
	std::string message;
	std::string command;
	uint16_t value;

	sendMessage("rd 0\n");

	message = getData();

	std::stringstream stream(message);
	stream >> command >> value;

	return value;
}

uint16_t FPGAAccess::getWindowsAddress()
{
	// TODO

	std::string message;
	std::string command;
	uint16_t value;

	sendMessage("rd 2\n");

	message = getData();

	std::stringstream stream(message);
	stream >> command >> value;

	return WINDOW_START_ADDRESS + (value * WINDOW_FULL_SIZE);
}

void FPGAAccess::readWindow(SpikeWindow *data)
{
	// TODO

	uint16_t addr = getWindowsAddress();

	// Retrieve the full window
	for (int i = 0; i < WINDOW_SIZE; i++) {
		std::stringstream sendStream;
		std::string message;
		std::string command;
		uint16_t unsignedData;

		sendStream << "rd " << (addr + i) << std::endl;

		sendMessage(sendStream.str());

		message = getData();

		// Actual received string is the binary data interpreted as an unsigned int,
		// so it's needed to pass through a temp unsigned to get the correct value.
		std::stringstream stream(message);
		stream >> command >> unsignedData;
		(*data)[i] = unsignedData;
	}

	sendMessage("wr 1 2\n");
}
