#ifndef COMMON_H
#define COMMON_H

#include <memory>
#include <queue>
#include "spike_detector.hpp"
#define MOVING_AVG_SIZE		128
#define MOVING_AVG_LOG2		7
#define DETECTION_FACTOR	15
#define WINDOW_AFTER_SPIKE_SIZE 100

typedef bool (*on_irq_trigger_t)(const std::queue<std::string> &,
				 SpikeDetector &);

typedef void (*on_window_read_t)(SpikeDetector &);

int getReferenceSpikes(const char *path,
		       std::queue<std::shared_ptr<SpikeWindow> > &result);

bool compareWindow(std::queue<std::shared_ptr<SpikeWindow> > &spikeRefFifo,
		   const SpikeWindow &window);

std::shared_ptr<FpgaAccessRemote> create_access(uint16_t port);
void test_read_window(SpikeDetector &detector,
		      std::queue<std::shared_ptr<SpikeWindow> > &spikes);

void test_file(const char *simulation_file, uint16_t port,
	       size_t expected_spike_nb, on_irq_trigger_t on_irq,
	       on_window_read_t on_window_read);

#define TEST_SETUP(simulation_file, server_port, handler, expected_spike_nb, \
		   spikes)                                                   \
	const char *input_file_path = realpath(simulation_file, NULL);       \
                                                                             \
	const SetupOptions opts = { .wait_for_connection = true,             \
				    .port = (server_port) };                 \
	auto access = std::make_shared<FpgaAccessRemote>(opts);              \
                                                                             \
	ASSERT_EQ(getReferenceSpikes(input_file_path, spikes), 0);           \
	const size_t expected_spikes = spikes.size();                        \
	ASSERT_EQ(expected_spikes, expected_spike_nb);                       \
                                                                             \
	SpikeDetector detector{ access, handler };                           \
	detector.set_simulation_file(input_file_path);                       \
	ASSERT_FALSE(detector.is_data_ready());                              \
	ASSERT_FALSE(detector.is_acquisition_in_progress());

#define TEST_WINDOW(detector, spikes)                                      \
	do {                                                               \
		SpikeWindow window;                                        \
		ASSERT_EQ(detector.get_window_address() & 0xF0FF, 0x1000); \
		ASSERT_TRUE(detector.is_data_ready());                     \
		ASSERT_TRUE(detector.read_window(window));                 \
		ASSERT_TRUE(compareWindow(spikes, window));                \
	} while (0);

#endif
