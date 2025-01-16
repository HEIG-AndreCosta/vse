#ifndef FPGAACCESSREMOTE_H
#define FPGAACCESSREMOTE_H

#include "fpgaaccess.hpp"
#include <cstdint>
#include <queue>
#include <condition_variable>
#include <mutex>
#include <thread>

class FpgaAccessRemote : public FpgaAccess {
    public:

	void setup();
	void write_register(uint16_t reg, uint16_t value);
	uint16_t read_register(uint16_t reg);
	void set_callback(irq_handler_t);

    private:
	FpgaAccessRemote();
	~FpgaAccessRemote();

	void *connectionHandler(void *socket_desc);

	void waitConnection();

	void *server();

	void receiver();

	void do_send(const std::string &buffer);
	std::string do_receive();

	std::string getData();

	int sock = 0;

	std::thread fpgaServerThread;
	std::thread receiverThread;
	std::queue<std::string> receivedFifo;

	std::condition_variable receivedCondVar;
	std::mutex receiveMutex;

	irq_handler_t handler;
};

#endif // FPGAACCESSREMOTE_H
