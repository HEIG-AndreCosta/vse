#include "mock/mock_fpga_access.hpp"
#include "spike_detector.hpp"
#include <cstdint>
#include <gtest/gtest.h>
#include <string>
#include <vector>

static void handler(const std::string &message)
{
}

TEST(TestSpikeDetector, SetupGetsCalledAndHandlerGetsSet)
{
	std::vector<Register> v;
	auto access = std::make_shared<MockFpgaAccess>(v);

	SpikeDetector sd = { access, handler };

	ASSERT_TRUE(access->setup_called);
	ASSERT_EQ(handler, access->handler);
}
TEST(TestSpikeDetector, StartStopAcquisition)
{
	std::vector<Register> v;
	auto access = std::make_shared<MockFpgaAccess>(v);

	SpikeDetector sd = { access, handler };
	sd.start_acquisition();
	sd.stop_acquisition();

	ASSERT_EQ(access->access.size(), 2);

	ASSERT_FALSE(access->access[0].is_read);
	ASSERT_EQ(access->access[0].reg, 1);
	ASSERT_EQ(access->access[0].value, 1);

	ASSERT_FALSE(access->access[1].is_read);
	ASSERT_EQ(access->access[1].reg, 1);
	ASSERT_EQ(access->access[1].value, 0);
}

TEST(TestSpikeDetector, TestAcquisitionInProgress)
{
	std::vector<Register> v{ Register{ 0, 0 } };
	auto access = std::make_shared<MockFpgaAccess>(v);

	SpikeDetector sd = { access, handler };
	ASSERT_FALSE(sd.is_acquisition_in_progress());
	v[0].value = 1;
	ASSERT_FALSE(sd.is_acquisition_in_progress());
	v[0].value = 2;
	ASSERT_TRUE(sd.is_acquisition_in_progress());
	v[0].value = 3;
	ASSERT_TRUE(sd.is_acquisition_in_progress());

	ASSERT_EQ(access->access.size(), 4);

	for (const auto &a : access->access) {
		ASSERT_EQ(a.reg, 0);
		ASSERT_TRUE(a.is_read);
	}
}

TEST(TestSpikeDetector, TestDataReady)
{
	std::vector<Register> v{ Register{ 0, 0 } };
	auto access = std::make_shared<MockFpgaAccess>(v);

	SpikeDetector sd = { access, handler };
	ASSERT_FALSE(sd.is_data_ready());
	v[0].value = 1;
	ASSERT_TRUE(sd.is_data_ready());
	v[0].value = 2;
	ASSERT_FALSE(sd.is_data_ready());
	v[0].value = 3;
	ASSERT_TRUE(sd.is_data_ready());

	ASSERT_EQ(access->access.size(), 4);

	for (const auto &a : access->access) {
		ASSERT_EQ(a.reg, 0);
		ASSERT_TRUE(a.is_read);
	}
}

TEST(TestSpikeDetector, TestStatus)
{
	std::vector<Register> v{ Register{ 0, 0 } };
	auto access = std::make_shared<MockFpgaAccess>(v);

	SpikeDetector sd = { access, handler };
	for (uint16_t i = 0; i <= 3; ++i) {
		ASSERT_EQ(v[0].value, sd.get_status());
	}

	ASSERT_EQ(access->access.size(), 4);

	for (const auto &a : access->access) {
		ASSERT_EQ(a.reg, 0);
		ASSERT_TRUE(a.is_read);
	}
}

TEST(TestSpikeDetector, TestReadWindow)
{
	const uint16_t WINDOW_START_ADDR = 0x1000;
	std::vector<Register> v{ Register{ 0, 1 },
				 Register{ 2, WINDOW_START_ADDR } };

	for (size_t i = 0; i < WINDOW_SIZE; ++i) {
		v.emplace_back(WINDOW_START_ADDR + i, i);
	}

	auto access = std::make_shared<MockFpgaAccess>(v);

	SpikeDetector sd = { access, handler };

	SpikeWindow window;

	ASSERT_TRUE(sd.read_window(window));

	for (size_t i = 0; i < WINDOW_SIZE; ++i) {
		ASSERT_EQ(window[i], i);
	}

	ASSERT_EQ(access->access.size(), 2 + WINDOW_SIZE);
	ASSERT_EQ(access->access[0].reg, 0);
	ASSERT_EQ(access->access[1].reg, 2);
	ASSERT_TRUE(access->access[0].is_read);
	ASSERT_TRUE(access->access[1].is_read);
}
