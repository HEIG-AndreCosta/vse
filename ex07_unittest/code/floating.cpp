
#include <cmath>

#include <gtest/gtest.h>

/// Shows the potential rounding of floating point values.
/// For doing so, try to compare almost similar values with EXPECT_FLOAT_EQ()
///
TEST(Floating, testRounding)
{
	double a = 0.01;
	double b = 0.010000001;

	EXPECT_FLOAT_EQ(a, b);
}

///
/// Compute the average of square root numbers in [1, 10] in two different ways:
/// - Do the sum, then divide by 10.
/// - Do the sum of the square roots divided by 10.
///
/// Compare with ASSERT_EQ et ASSERT_FLOAT_EQ. What happens?
///
TEST(Floating, Loop)
{
	double sum = 0;
	for (int i = 1; i <= 10; ++i) {
		sum += sqrt(i);
	}
	const double avg = sum / 10.;

	sum = 0;
	for (int i = 1; i <= 10; ++i) {
		sum += (sqrt(i) / 10.);
	}

	EXPECT_EQ(sum, avg);
	EXPECT_FLOAT_EQ(sum, avg);
}
