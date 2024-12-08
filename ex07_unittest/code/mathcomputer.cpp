

#include <gtest/gtest.h>

typedef unsigned int datatype_t;

class MathComputer {
    public:
	MathComputer(int N)
		: N(N)
	{
	}

	///
	/// \brief Computes a mathematical function
	/// \param a First parameter
	/// \param b Second paramter
	/// \param c Third parameter
	/// \return a**N + b * c
	///
	/// This function returns a power of N plus b times c
	///
	datatype_t compute(datatype_t a, datatype_t b, datatype_t c)
	{
		datatype_t result = 1;
		for (int i = 0; i < N; i++) {
			result *= a;
		}
		result += b * c;
		return result;
	}

    private:
	int N{ 0 };
};

TEST(Computer, simpleComputation)
{
	auto computer = MathComputer(1);
	ASSERT_EQ(computer.compute(1, 1, 1), 1);

	ASSERT_EQ(computer.compute(0, 1, 1), 0);
	ASSERT_EQ(computer.compute(1, 0, 1), 0);
	ASSERT_EQ(computer.compute(1, 1, 0), 0);
}
