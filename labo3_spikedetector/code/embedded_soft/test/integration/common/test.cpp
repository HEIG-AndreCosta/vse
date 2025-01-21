#include "common.h"
#include <condition_variable>
#include "spike_detector.hpp"
#include "fpgaaccessremote.hpp"
#include <cstdint>
#include <gtest/gtest.h>
#include <cstddef>
#include <mutex>
#include <queue>

static std::mutex irqMutex;
static std::condition_variable irqCondVar;
static std::queue<std::string> irqFifo;

static void handler(const std::string &message)
{
	irqFifo.push(message);
	irqCondVar.notify_all();
}

static void test_window(SpikeDetector &detector,
			std::queue<std::shared_ptr<SpikeWindow> > &spikes)
{
	SpikeWindow window;
	ASSERT_EQ(detector.get_window_address() & 0xF0FF, 0x1000);
	ASSERT_TRUE(detector.is_data_ready());
	ASSERT_TRUE(detector.read_window(window));
	ASSERT_TRUE(compareWindow(spikes, window));
}
void test_file(const char *simulation_file, uint16_t port,
	       size_t expected_spike_nb, on_irq_trigger_t on_irq,
	       on_window_read_t on_window_read)
{
	std::queue<std::shared_ptr<SpikeWindow> > spikes;

	const char *input_file_path = realpath(simulation_file, NULL);

	const SetupOptions opts = { .wait_for_connection = true, .port = port };
	auto access = std::make_shared<FpgaAccessRemote>(opts);

	ASSERT_EQ(getReferenceSpikes(input_file_path, spikes), 0);
	const size_t expected_spikes = spikes.size();
	ASSERT_EQ(expected_spikes, expected_spike_nb);

	SpikeDetector detector{ access, handler };
	detector.set_simulation_file(input_file_path);
	ASSERT_FALSE(detector.is_data_ready());
	ASSERT_FALSE(detector.is_acquisition_in_progress());

	detector.start_acquisition();
	ASSERT_TRUE(detector.is_acquisition_in_progress());

	std::unique_lock<std::mutex> lk(irqMutex);

	while (irqCondVar.wait_for(lk, std::chrono::seconds(600),
				   [] { return !irqFifo.empty(); })) {
		std::string value = irqFifo.back();
		irqFifo.pop();
		if (strstr(value.c_str(), "end")) {
			break;
		}

		if (on_irq(irqFifo, detector)) {
			test_window(detector, spikes);
			on_window_read(detector);
		}
	}
	detector.stop_acquisition();
	ASSERT_FALSE(detector.is_acquisition_in_progress());

	while (detector.is_data_ready()) {
		test_window(detector, spikes);
		on_window_read(detector);
	}
	ASSERT_EQ(spikes.size(), 0);
}
