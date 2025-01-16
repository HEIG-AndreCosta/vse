#ifndef FPGAACCESSREMOTE_H
#define FPGAACCESSREMOTE_H

#include "fpgaaccess.hpp"
#include <cstdint>
#include <vector>

struct Access {
	bool is_read;
	int reg;
	int value;
};
struct Register {
	uint16_t address;
	uint16_t value;

	Register(uint16_t address, uint16_t value)
		: address(address)
		, value(value)
	{
	}
};

class MockFpgaAccess : public FpgaAccess {
    public:
	MockFpgaAccess(const std::vector<Register> &registers);
	~MockFpgaAccess() = default;

	void setup();
	void write_register(uint16_t reg, uint16_t value);

	uint16_t read_register(uint16_t reg);
	void set_callback(irq_handler_t);

	std::vector<Access> access;
	const std::vector<Register> &registers;
	bool setup_called;
	irq_handler_t handler;

    private:
};

#endif // FPGAACCESSREMOTE_H
