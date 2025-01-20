
#include <cstdint>
#include <gtest/gtest.h>
#include "common/common.h"
#include "spike_detector.hpp"
#include <queue>

static bool on_irq_read_window(const std::queue<std::string> &fifo,
			       SpikeDetector &detector)
{
	(void)detector;
	return true;
}

static bool on_irq_dont_read(const std::queue<std::string> &fifo,
			     SpikeDetector &detector)
{
	(void)detector;
	return false;
}

static bool on_irq_stop_acquisition(const std::queue<std::string> &fifo,
				    SpikeDetector &detector)
{
	detector.stop_acquisition();
	return true;
}

static void on_window_read_do_nothing(SpikeDetector &detector)
{
	(void)detector;
}

static void on_window_read_restart_acquisition(SpikeDetector &detector)
{
	detector.start_acquisition();
}
static uint16_t port_from_env()
{
	return static_cast<uint16_t>(std::stoi(getenv("SERVER_PORT")));
}
TEST(Integration, RandomSpikes)
{
	std::cout << "Port " << port_from_env() << std::endl;
	test_file("../../../../simulation_files/input_values.txt",
		  port_from_env(), 52, on_irq_read_window,
		  on_window_read_do_nothing);
}

TEST(Integration, LinearNoSpikes)
{
	std::cout << "Port " << port_from_env() << std::endl;
	test_file("../../../../simulation_files/linear.txt", port_from_env(), 0,
		  on_irq_read_window, on_window_read_do_nothing);
}

TEST(Integration, Zeros)
{
	std::cout << "Port " << port_from_env() << std::endl;
	test_file("../../../../simulation_files/zeros.txt", port_from_env(), 0,
		  on_irq_read_window, on_window_read_do_nothing);
}

TEST(Integration, StopAcquisitionsWhileReading)
{
	std::cout << "Port " << port_from_env() << std::endl;
	test_file("../../../../simulation_files/constant_spikes_16_windows.txt",
		  port_from_env(), 16, on_irq_stop_acquisition,
		  on_window_read_restart_acquisition);
}

TEST(Integration, AccumulateAndReadAtTheEnd)
{
	std::cout << "Port " << port_from_env() << std::endl;
	test_file("../../../../simulation_files/constant_spikes_16_windows.txt",
		  port_from_env(), 16, on_irq_stop_acquisition,
		  on_window_read_restart_acquisition);
}
