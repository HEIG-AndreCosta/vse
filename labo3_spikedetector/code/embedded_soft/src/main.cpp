#include "fpgaaccessremote.hpp"

#include <iostream>
#include "spike_detector.hpp"
#include <memory>
#include <unistd.h>
#include <mutex>
#include <queue>
#include <cstring>

#define MOVING_AVG_SIZE		128
#define MOVING_AVG_LOG2		7
#define DETECTION_FACTOR	15
#define WINDOW_AFTER_SPIKE_SIZE 100

std::mutex irqMutex;
std::condition_variable irqCondVar;
std::queue<std::string> irqFifo;

std::queue<std::shared_ptr<SpikeWindow> > spikeRefFifo;

static void handler(const std::string &message)
{
	std::cout << "Received new IRQ: " << message << std::endl;
	irqFifo.push(message);
	irqCondVar.notify_all();
}

/**
 * Compute the reference spike to be able to compare the result got from the FPGA.
 * The calculs mimiq the ones in the FPGA to have the same rounding due to optimization.
 */
int getReferenceSpikes(const char *path)
{
	FILE *file;
	int val;
	int line = 0;
	int saveSpikeCnt = -1;

	int16_t window[WINDOW_SIZE];
	uint16_t idx = 0;
	int64_t sum = 0;
	int64_t average = 0;
	uint64_t squareSum = 0;
	uint64_t squareStdDev = 0;
	uint64_t deviation = 0;

	file = fopen(path, "r");
	if (!file) {
		std::cerr << "Couldn't open " << path << '\n';
		return -1;
	}

	while (!feof(file)) {
		fscanf(file, "%d", &val);
		line++;

		// window is use like a circular buffer to avoid having to move all data each time.
		// It means that the first sample is at idx offset.
		window[idx] = val;
		idx = (idx + 1) % WINDOW_SIZE;

		deviation = val - average;

		if (line <= MOVING_AVG_SIZE) {
			// Do not remove old values or detect spike before the moving average is full
			sum += val;
			average = sum >> MOVING_AVG_LOG2;
			squareSum += val * val;
			squareStdDev = (squareSum >> MOVING_AVG_LOG2) -
				       (average * average);
		} else {
			if (saveSpikeCnt == -1) {
				// Currently not saving a spike, detect any new one.
				if ((deviation * deviation) >
				    (squareStdDev * DETECTION_FACTOR)) {
					// Set counter to get all needed sample
					// -2 is to take into account that the count end at 0
					// and that current sample is the first one.
					saveSpikeCnt =
						WINDOW_AFTER_SPIKE_SIZE - 2;
				}
			} else if (saveSpikeCnt == 0) {
				std::shared_ptr<SpikeWindow> spike =
					std::make_shared<SpikeWindow>();

				// Copy the samples into the spike in the correct order. first from idx to then end, then 0 to idx-1
				std::memcpy(&(*spike)[0], &window[idx],
					    (WINDOW_SIZE - idx) *
						    sizeof(int16_t));
				std::memcpy(&(*spike)[WINDOW_SIZE - idx],
					    window, idx * sizeof(int16_t));

				spikeRefFifo.push(spike);
				saveSpikeCnt = -1;
			} else {
				saveSpikeCnt--;
			}

			sum += deviation;
			average = sum >> MOVING_AVG_LOG2;
			squareSum +=
				(val * val) - (squareSum >> MOVING_AVG_LOG2);
			squareStdDev = (squareSum >> MOVING_AVG_LOG2) -
				       (average * average);
		}
	}

	std::cout << "Detected " << spikeRefFifo.size() << " spikes"
		  << std::endl;

	fclose(file);
	return 0;
}

bool compareWindow(SpikeWindow *window)
{
	bool valid = true;

	if (spikeRefFifo.empty()) {
		std::cout << "Not enough reference spikes" << std::endl;
		return false;
	}

	std::shared_ptr<SpikeWindow> ref = spikeRefFifo.front();
	spikeRefFifo.pop();

	for (int i = 0; i < WINDOW_SIZE; i++) {
		if ((*ref)[i] != (*window)[i]) {
			valid = false;
			std::cout << "Error at index " << i
				  << ". Expected: " << (*ref)[i]
				  << " got: " << (*window)[i] << std::endl;
		}
	}

	return valid;
}

int main(int argc, char **argv)
{
	if (argc < 2) {
		std::cout << "Usage " << argv[0] << " <spike_data_file>\n";
		return 1;
	}
	int err = getReferenceSpikes(argv[1]);
	if (err < 0) {
		return 1;
	}

	auto access = std::make_shared<FpgaAccessRemote>();

	SpikeDetector detector{ access, handler };

	std::unique_lock<std::mutex> lk(irqMutex);

	std::cout << "Current status: " << detector.get_status() << std::endl;

	std::cout << "Starting acquisition" << std::endl;
	detector.start_acquisition();
	std::cout << "Current status: " << detector.get_status() << std::endl;

	while (irqCondVar.wait_for(lk, std::chrono::seconds(600),
				   [] { return !irqFifo.empty(); })) {
		SpikeWindow window;

		std::cout << "New window at address: "
			  << detector.get_window_address() << std::endl;
		std::cout << "Reading window" << std::endl;

		detector.read_window(window);
		irqFifo.pop();

		if (compareWindow(&window)) {
			std::cout << "Window is valid" << std::endl;
		} else {
			std::cout << "Window is not valid" << std::endl;
		}
	}

	std::cout << "Stoping acquisition" << std::endl;
	detector.stop_acquisition();
	std::cout << "Current status: " << detector.get_status() << std::endl;

	return EXIT_SUCCESS;
}
