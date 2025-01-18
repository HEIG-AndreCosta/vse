#include <cassert>
#include <gtest/gtest.h>
#include "mock_fpga_access.hpp"
MockFpgaAccess::MockFpgaAccess(const std::vector<Register> &registers)
	: setup_called(false)
	, access()
	, registers(registers)
{
}
void MockFpgaAccess::setup()
{
	setup_called = true;
}
void MockFpgaAccess::write_register(uint16_t reg, uint16_t value)
{
	access.push_back(Access{
		.is_read = false,
		.reg = reg,
		.value = value,
	});
}

uint16_t MockFpgaAccess::read_register(uint16_t reg)
{
	for (const auto &r : registers) {
		if (r.address == reg) {
			access.push_back(Access{
				.is_read = true,
				.reg = reg,
				.value = r.value,
			});

			return r.value;
		}
	}
	return 0xFFFF;
}
void MockFpgaAccess::set_callback(irq_handler_t cb)
{
	handler = cb;
}
