
#include <gtest/gtest.h>
#include "common/common.h"
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

TEST(Integration, RandomSpikes)
{
	test_file("../../../../simulation_files/input_values.txt", 8888, 51,
		  on_irq_read_window, on_window_read_do_nothing);
}

TEST(Integration, LinearNoSpikes)
{
	test_file("../../../../simulation_files/linear.txt", 8889, 0,
		  on_irq_read_window, on_window_read_do_nothing);
}

TEST(Integration, Zeros)
{
	test_file("../../../../simulation_files/input_values.txt", 8890, 0,
		  on_irq_read_window, on_window_read_do_nothing);
}

TEST(Integration, StopAcquisitionsWhileReading)
{
	test_file("../../../../simulation_files/constant_spikes_16_windows.txt",
		  8891, 0, on_irq_stop_acquisition,
		  on_window_read_restart_acquisition);
}

TEST(Integration, AccumulateAndReadAtTheEnd)
{
	test_file("../../../../simulation_files/constant_spikes_16_windows.txt",
		  8889, 0, on_irq_stop_acquisition,
		  on_window_read_restart_acquisition);
}
