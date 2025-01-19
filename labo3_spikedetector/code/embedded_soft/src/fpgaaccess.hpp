#include <cstdint>
#include <string>

/**
 * Type for the IRQ handler function.
 * That handler should NOT block as it will by directly called
 * by the receiving thread. And so, if blocked, no new message
 * will be received, which can lead to deadlocks.
 */
typedef void (*irq_handler_t)(const std::string &);

class FpgaAccess {
    public:
	virtual void setup() = 0;
	virtual void write_register(uint16_t reg, uint16_t value) = 0;
	virtual uint16_t read_register(uint16_t reg) = 0;
	virtual void set_callback(irq_handler_t) = 0;
	virtual void set_simulation_file(const char *path) = 0;
};
