#ifndef FPGAACCESSREMOTE_H
#define FPGAACCESSREMOTE_H

#include "fpgaaccess.hpp"
#include <cstdint>
#include <queue>
#include <condition_variable>
#include <mutex>
#include <thread>

struct SetupOptions {
	bool wait_for_connection;
	uint16_t port;
};

class FpgaAccessRemote : public FpgaAccess {
    public:
	FpgaAccessRemote(SetupOptions opts);
	~FpgaAccessRemote();

	void setup();
	void write_register(uint16_t reg, uint16_t value);
	uint16_t read_register(uint16_t reg);
	void set_callback(irq_handler_t);
	void set_simulation_file(const char *path);

    private:
	void *connectionHandler(void *socket_desc);

	void wait_connection();

	void start_server(uint16_t port);
	void *accept_connection(int sockfd);

	void receiver();

	void do_send(const std::string &buffer);
	std::string do_receive();

	std::string getData();

	int sock = 0;
	SetupOptions opts;

	std::thread listener_thread;
	std::thread rx_thread;
	std::queue<std::string> receivedFifo;

	std::condition_variable receivedCondVar;
	std::mutex receiveMutex;

	irq_handler_t handler;
};

#endif // FPGAACCESSREMOTE_H
