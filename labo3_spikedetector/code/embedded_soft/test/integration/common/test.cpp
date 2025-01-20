#include "common.h"
#include <condition_variable>
#include "spike_detector.hpp"
#include <cstdint>
#include <gtest/gtest.h>
#include <iostream>
#include <cstddef>
#include <mutex>
#include <queue>

static std::mutex irqMutex;
static std::condition_variable irqCondVar;
static std::queue<std::string> irqFifo;

static void handler(const std::string &message)
{
	std::cout << "Received new IRQ: " << message << std::endl;
	irqFifo.push(message);
	irqCondVar.notify_all();
}

void test_file(const char *simulation_file, uint16_t port,
	       size_t expected_spike_nb, on_irq_trigger_t on_irq,
	       on_window_read_t on_window_read)
{
	size_t spike_nb = 0;
	std::queue<std::shared_ptr<SpikeWindow> > spikes;
	TEST_SETUP(simulation_file, port, handler, expected_spike_nb, spikes);

	detector.start_acquisition();
	ASSERT_TRUE(detector.is_acquisition_in_progress());

	std::unique_lock<std::mutex> lk(irqMutex);

	while (irqCondVar.wait_for(lk, std::chrono::seconds(600),
				   [] { return !irqFifo.empty(); })) {
		std::string value = irqFifo.back();
		if (value == "irq end\n") {
			break;
		}

		if (on_irq(irqFifo, detector)) {
			TEST_WINDOW(detector, spikes)
			on_window_read(detector);
			spike_nb++;
		}

		irqFifo.pop();
	}
	detector.stop_acquisition();
	ASSERT_FALSE(detector.is_acquisition_in_progress());

	while (detector.is_data_ready()) {
		TEST_WINDOW(detector, spikes);
		on_window_read(detector);
	}
	ASSERT_EQ(spikes.size(), 0);
}
