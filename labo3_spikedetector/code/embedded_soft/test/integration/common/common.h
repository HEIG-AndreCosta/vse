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

#endif
