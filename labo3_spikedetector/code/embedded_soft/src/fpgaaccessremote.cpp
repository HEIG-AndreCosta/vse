#include "fpgaaccessremote.hpp"

#include <cstdint>
#include <iostream>
#include <cstring>
#include <sstream>
#include <cstdlib>
#include <sys/socket.h>
#include <arpa/inet.h> //inet_addr
#include <unistd.h>

void *FpgaAccessRemote::accept_connection(int sockfd)
{
	struct sockaddr_in client;
	size_t c = sizeof(client);

	int client_sock =
		accept(sockfd, (struct sockaddr *)&client, (socklen_t *)&c);

	if (client_sock <= 0) {
		perror("accept failed");
		return NULL;
	}

	puts("Connection accepted");

	sock = client_sock;

	receivedCondVar.notify_all();

	return NULL;
}

void *FpgaAccessRemote::start_server(uint16_t port)
{
	int sockfd;
	int option = 1;
	struct sockaddr_in server;
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
	server.sin_port = htons(port);

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

	listener_thread =
		std::thread(&FpgaAccessRemote::accept_connection, this, sockfd);

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
		int err = shutdown(sock, SHUT_RDWR);
		if (err < 0) {
			std::cerr << "Shutdown error (" << err << ")\n";
		}
		close(sock);
	}

	if (listener_thread.joinable()) {
		listener_thread.join();
	}

	if (rx_thread.joinable()) {
		rx_thread.join();
	}
	std::cout << "Destructor over" << std::endl;
}

void FpgaAccessRemote::setup()
{
	SetupOptions opts = { .wait_for_connection = true, .port = 8888 };
	setup(opts);
}
void FpgaAccessRemote::setup(const SetupOptions &opts)
{
	start_server(opts.port);
	rx_thread = std::thread(&FpgaAccessRemote::receiver, this);

	if (opts.wait_for_connection) {
		wait_connection();
	}
}

void FpgaAccessRemote::wait_connection()
{
	std::unique_lock<std::mutex> lk(receiveMutex);

	receivedCondVar.wait(lk, [this] { return sock != 0; });
}

void FpgaAccessRemote::receiver()
{
	char clientMessage[2000];
	char messageCommand[2000];
	ssize_t read_size;

	wait_connection();

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

void FpgaAccessRemote::set_simulation_file(const char *path)
{
	std::stringstream stream;
	stream << "set_file" << path << std::endl;

	do_send(stream.str());
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
