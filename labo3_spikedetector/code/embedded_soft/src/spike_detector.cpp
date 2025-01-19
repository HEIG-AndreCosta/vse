#include "spike_detector.hpp"
#include "fpgaaccessremote.hpp"
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <unistd.h>

SpikeDetector::SpikeDetector(std::shared_ptr<FpgaAccess> access,
			     on_message_cb cb)
	: access(access)
{
	if (this->access) {
		this->access->setup();
	} else {
		throw std::invalid_argument("Access cannot be null");
	}

	if (cb) {
		this->set_on_new_data_callback(cb);
	} else {
		throw std::invalid_argument("Callback cannot be null");
	}
}
void SpikeDetector::set_simulation_file(const char *path)
{
	access->set_simulation_file(path);
}

bool SpikeDetector::is_data_ready()
{
	return !(get_status() & 1);
}

void SpikeDetector::start_acquisition()
{
	access->write_register(1, 1);
}
void SpikeDetector::stop_acquisition()
{
	access->write_register(1, 0);
}

void SpikeDetector::set_on_new_data_callback(on_message_cb cb)
{
	if (!cb) {
		throw std::invalid_argument("Callback cannot be null");
	}
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
	ack_window_read();
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
	return access->read_register(0);
}

uint16_t SpikeDetector::get_window_address()
{
	const uint16_t offset = access->read_register(2);
	return WINDOW_START_ADDRESS + (offset * WINDOW_FULL_SIZE);
}
