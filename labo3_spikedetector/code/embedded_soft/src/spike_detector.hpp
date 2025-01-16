#include "fpgaaccessremote.hpp"
#include <array>
#include <cstdint>
#include <memory>

#define WINDOW_START_ADDRESS 0x1000
#define WINDOW_SIZE	     150
#define WINDOW_FULL_SIZE     256

typedef std::array<int16_t, WINDOW_SIZE> SpikeWindow;

typedef void (*on_message_cb)(const std::string &);
class SpikeDetector {
    public:
	SpikeDetector(std::shared_ptr<FpgaAccess> access, on_message_cb cb);
	~SpikeDetector() = default;

	void start_acquisition();
	void stop_acquisition();
	bool is_acquisition_in_progress();
	bool is_data_ready();

	uint16_t get_status();
	uint16_t get_window_address();

	bool read_window(SpikeWindow &data);
	void set_on_new_data_callback(on_message_cb);

    private:
	std::shared_ptr<FpgaAccess> access;
	void read_window_internal(SpikeWindow &data);
	void ack_window_read();
};
