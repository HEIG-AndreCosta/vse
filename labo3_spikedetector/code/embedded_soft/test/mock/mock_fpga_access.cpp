
#include "mock_fpga_access.hpp"
MockFpgaAccess::MockFpgaAccess()
	: setup_called(false)
	, access()
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
	access.push_back(Access{
		.is_read = true,
		.reg = reg,
		.value = 0,
	});
	return 0;
}
void MockFpgaAccess::set_callback(irq_handler_t cb)
{
	handler = cb;
}
