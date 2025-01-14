#include "spike_detector.hpp"
#include "fpgaaccessremote.hpp"
#include <cstdint>
#include <memory>

SpikeDetector::SpikeDetector(std::unique_ptr<FpgaAccess> access,
			     on_message_cb cb)
	: access(std::move(access))
{
	access->setup();
	this->set_on_new_data_callback(cb);
}

bool SpikeDetector::is_data_ready()
{
	return get_status() & 1;
}

void SpikeDetector::set_on_new_data_callback(on_message_cb cb)
{
	access->set_callback(cb);
}

bool SpikeDetector::read_window(SpikeWindow &data)
{
	if (!is_data_ready()) {
		return false;
	}

	read_window_internal(data);
	return true;
}
void SpikeDetector::read_window_blocking(SpikeWindow &data)
{
	while (!is_data_ready())
		;

	read_window_internal(data);
}

void SpikeDetector::read_window_internal(SpikeWindow &data)
{
	const uint16_t window_address = get_window_address();

	// Retrieve the full window
	for (int i = 0; i < WINDOW_SIZE; i++) {
		std::string message;
		std::string command;
		const uint16_t register_data =
			access->read_register(window_address + i);

		data[i] = register_data;
	}
}
void SpikeDetector::ack_window_read()
{
	access->write_register(1, 2);
}
bool SpikeDetector::is_acquisition_in_progress()
{
	return get_status() & 2;
}

uint16_t SpikeDetector::get_status()
{
	const uint16_t value = access->read_register(0);
	return value;
}

uint16_t SpikeDetector::get_window_address()
{
	const uint16_t offset = access->read_register(2);
	return WINDOW_START_ADDRESS + (offset * WINDOW_FULL_SIZE);
}
