#include "fpgaaccessremote.hpp"

#include <cstdint>
#include <iostream>
#include <cstring>
#include <sstream>
#include <cstdlib>
#include <sys/socket.h>
#include <arpa/inet.h> //inet_addr
#include <unistd.h>

void *FpgaAccessRemote::server()
{
	int sockfd, client_sock, c;
	int option = 1;
	struct sockaddr_in server, client;
	//Create socket
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	if (sockfd == -1) {
		printf("Could not create socket");
	}

	setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, (char *)&option,
		   sizeof(option));

	puts("Socket created");

	//Prepare the sockaddr_in structure
	server.sin_family = AF_INET;
	server.sin_addr.s_addr = INADDR_ANY;
	server.sin_port = htons(8888);

	//Bind
	if (bind(sockfd, (struct sockaddr *)&server, sizeof(server)) < 0) {
		//print the error message
		perror("bind failed. Error");
		return NULL;
	}
	puts("bind done");

	//Listen
	listen(sockfd, 3);

	//Accept and incoming connection
	puts("Waiting for incoming connections...");
	c = sizeof(struct sockaddr_in);

	client_sock =
		accept(sockfd, (struct sockaddr *)&client, (socklen_t *)&c);

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
void *FpgaAccessRemote::connectionHandler(void *socket_desc)
{
	//Get the socket descriptor
	return nullptr;
}
FpgaAccessRemote::~FpgaAccessRemote()
{
	if (sock != 0) {
		this->do_send("end_test\n");
		// Sleep to be sure that data are correctly send
		sleep(5);
		shutdown(sock, SHUT_RDWR);
	}

	if (fpgaServerThread.joinable())
		fpgaServerThread.join();

	if (receiverThread.joinable())
		receiverThread.join();
}

void FpgaAccessRemote::setup()
{
	fpgaServerThread = std::thread(&FpgaAccessRemote::server, this);
	receiverThread = std::thread(&FpgaAccessRemote::receiver, this);
	waitConnection();
}

void FpgaAccessRemote::waitConnection()
{
	std::unique_lock<std::mutex> lk(receiveMutex);

	receivedCondVar.wait(lk, [this] { return sock != 0; });
}

void FpgaAccessRemote::receiver()
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

std::string FpgaAccessRemote::getData()
{
	std::string message;
	std::unique_lock<std::mutex> lk(receiveMutex);

	receivedCondVar.wait(lk, [this] { return !receivedFifo.empty(); });

	message = receivedFifo.front();
	receivedFifo.pop();

	return message;
}

void FpgaAccessRemote::do_send(const std::string &buffer)
{
	write(sock, buffer.data(), buffer.size());
}
std::string FpgaAccessRemote::do_receive()
{
	std::string message;
	std::unique_lock<std::mutex> lk(receiveMutex);

	receivedCondVar.wait(lk, [this] { return !receivedFifo.empty(); });

	message = receivedFifo.front();
	receivedFifo.pop();

	return message;
}

void FpgaAccessRemote::write_register(uint16_t reg, uint16_t value)
{
	std::stringstream stream;
	stream << "wr " << reg << " " << value << std::endl;
	this->do_send(stream.str());
}

uint16_t FpgaAccessRemote::read_register(uint16_t reg)
{
	{
		std::stringstream stream;
		stream << "rd " << reg << std::endl;
		this->do_send(stream.str());
	}

	std::string command;
	uint16_t value;

	const std::string message = this->do_receive();
	std::stringstream stream(message);
	stream >> command >> value;

	return value;
}

void FpgaAccessRemote::set_callback(irq_handler_t handler)
{
	this->handler = handler;
}
