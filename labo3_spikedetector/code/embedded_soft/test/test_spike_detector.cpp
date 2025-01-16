#include "mock/mock_fpga_access.hpp"
#include "spike_detector.hpp"
#include <gtest/gtest.h>
#include <string>

void handler(const std::string &message)
{
}

TEST(TestSpikeDetector, SetupGetsCalled)
{
	auto access = std::make_unique<MockFpgaAccess>();

	SpikeDetector sd = { std::move(access), handler };

	ASSERT_TRUE(access->setup_called);
	ASSERT_EQ(handler, access->handler);
}
