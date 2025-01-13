#ifndef FPGAACCESSREMOTE_H
#define FPGAACCESSREMOTE_H

#include <cstdint>
#include <queue>
#include <condition_variable>
#include <mutex>
#include <thread>
#include <array>

#define WINDOW_START_ADDRESS 0x1000
#define WINDOW_SIZE 150
#define WINDOW_FULL_SIZE 256

typedef std::array<int16_t, WINDOW_SIZE> SpikeWindow;

/**
 * Type for the IRQ handler function.
 * That handler should NOT block as it will by directly called
 * by the receiving thread. And so, if blocked, no new message
 * will be received, which can lead to deadlocks.
 */
typedef void (*irq_handler_t)(std::string &);

class FPGAAccess
{
public:
    static FPGAAccess& getInstance();

    FPGAAccess();
    ~FPGAAccess();

    void startAcquisition();

    void stopAcquisition();

    void setInterruptHandler(irq_handler_t handler);

    uint16_t getStatus();

    uint16_t getWindowsAddress();
    void readWindow(SpikeWindow *data);

    void init();



private:

    void *connectionHandler(void *socket_desc);

    void waitConnection();

    void *server();

    void receiver();

    std::string getData();
    void sendMessage(const std::string &message);
    void sendMessage(const char *message);

    int sock = 0;

    std::thread fpgaServerThread;
    std::thread receiverThread;
    std::queue<std::string> receivedFifo;

    std::condition_variable receivedCondVar;
    std::mutex receiveMutex;

    irq_handler_t handler;
};

#endif // FPGAACCESSREMOTE_H
