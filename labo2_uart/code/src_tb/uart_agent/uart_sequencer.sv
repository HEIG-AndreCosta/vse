/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : uart_sequencer.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the sequencer responsible for generating the
              data test on RX

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/

`ifndef UART_SEQUENCER_SV
`define UART_SEQUENCER_SV

class uart_sequencer #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  int testcase;
  logic [DATASIZE-1:0] data;

  uart_fifo_t sequencer_to_driver_fifo;

  task run_all_scenarios;
    test_write;
    test_read;
    test_fifo_empty;
    test_fifo_full;
    test_rx_fifo_full;
    test_boundaries;
    test_correct_clk_per_bit;
    test_random;
    test_stress;
    test_stress_rx;
  endtask

  /// Test duv write
  task test_write();
    //Nothing to do here
  endtask

  // Test Boundaries
  // This tests sending and receiving payloads full of zeros
  // and full of ones
  task test_boundaries;
    automatic uart_transaction trans;
    trans = new;
    trans.transaction_type = UART_TX_DUV_RX;
    trans.data = 0;
    sequencer_to_driver_fifo.put(trans);

    trans = new;
    trans.transaction_type = UART_TX_DUV_RX;
    trans.data = -1;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Test DUV Read
  // This tests receiving a payload
  task test_read;
    automatic uart_transaction trans = new;
    trans.transaction_type = UART_TX_DUV_RX;
    trans.data = 20'h12345;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Test DUV fifo empty
  task test_fifo_empty;
    //Don't do anything else the rx fifo won't be empty
  endtask

  // Test DUV TX fifo empty
  task test_fifo_full;
    // Nothing to do here
  endtask

  // Test DUV write/read clk per bit register
  task test_correct_clk_per_bit;
    // Nothing to do here
  endtask

  // Test DUV rx fifo full
  // This tests that the fifo can correctly set its
  // rx fifo full flag to true
  task test_rx_fifo_full;
    automatic uart_transaction trans;
    // Send FIFOSIZE payloads
    for (int i = 0; i < FIFOSIZE; ++i) begin
      trans = new;
      trans.transaction_type = UART_TX_DUV_RX;
      trans.data = i;
      sequencer_to_driver_fifo.put(trans);
    end
  endtask

  // Utility function to send FIFOSIZE payloads with a certain baudrate
  // at a 1 payload / second rate
  task test_bad_baudrate(logic [31:0] baudrate);
    automatic uart_transaction trans;
    // This loop simulates a device that would send a message every second
    // with the incorrect baudrate
    for (int i = 0; i < FIFOSIZE; ++i) begin
      trans = new;
      trans.transaction_type = UART_TX_DUV_RX_MODIFY_BAUDRATE;
      trans.baudrate = baudrate;
      trans.data = 20'h12345 << i;
      sequencer_to_driver_fifo.put(trans);
      //Wait a bit to see if the duv can recover
      trans = new;
      trans.transaction_type = UART_WAIT;
      trans.data = 1_000_000_000;
      sequencer_to_driver_fifo.put(trans);
    end

  endtask

  // Test random
  // Tests receiving and sending random payloads
  // It's also a good stress test as the duv is constantly sending and
  // receiving data
  // This test is driven by coverage
  task test_random;
    automatic uart_transaction coverage_trans = new;
    while (coverage_trans.cov_group.get_inst_coverage() < 100) begin
      automatic uart_transaction trans = new;

      assert (coverage_trans.randomize())
      else $fatal("No solutions for trans.randomize");
      coverage_trans.cov_group.sample();

      trans.transaction_type = UART_TX_DUV_RX;
      trans.data = coverage_trans.data;
      sequencer_to_driver_fifo.put(trans);
      //trans = new;
      //trans.transaction_type = UART_WAIT;
      //trans.data = 500_000_000;
      //sequencer_to_driver_fifo.put(trans);
    end
  endtask

  // Stress test
  // This stress tests the duv tx part
  task test_stress;
  endtask

  // Stress test
  // This stress tests the duv rx part
  task test_stress_rx;
    automatic uart_transaction trans;
    for (int i = 0; i < FIFOSIZE * 10; ++i) begin
      trans = new;
      trans.transaction_type = UART_TX_DUV_RX;
      trans.data = i;
      sequencer_to_driver_fifo.put(trans);
    end
  endtask

  // Test what happens if the baudrate is too high
  // For reference, we use 9600 baudrate for testing
  // This test should not be run automatically but it may be useful to know
  // what happens if the other device isn't set with the correct baudrate
  task test_baudrate_too_high;
    for (logic [31:0] baudrate = 9600; baudrate < 10600; baudrate += 100) begin
      $display("%t [UART Sequencer] Testing with baudrate %d", $time, baudrate);
      test_bad_baudrate(baudrate);
    end
    // Also see what happens with 115200 baudrate since it's a pretty standard baudrate
    $display("%t [UART Sequencer] Testing with baudrate 115200", $time);
    test_bad_baudrate(115200);
  endtask

  // Test what happens if the baudrate is too low
  // For reference, we use 9600 baudrate for testing
  // This test should not be run automatically but it may be useful to know
  // what happens if the other device isn't set with the correct baudrate
  task test_baudrate_too_low;
    for (logic [31:0] baudrate = 9600; baudrate > 8600; baudrate -= 100) begin
      $display("%t [UART Sequencer] Testing with baudrate %d", $time, baudrate);
      test_bad_baudrate(baudrate);
    end
  endtask

  task run;
    $display("%t [UART Sequencer] Testcase %d", $time, testcase);
    case (testcase)
      0: run_all_scenarios;
      1: test_write;
      2: test_read;
      3: test_fifo_empty;
      4: test_fifo_full;
      5: test_rx_fifo_full;
      6: test_boundaries;
      7: test_correct_clk_per_bit;
      8: test_random;
      9: test_stress;
      10: test_stress_rx;
      // Baudrate tests are not run automatically since they are expected to
      // generate errors. They exist to be run manually and checked by
      // a human.
      11: test_baudrate_too_high;
      12: test_baudrate_too_low;
      default: $display("Invalid test case %d", testcase);
    endcase
    $display("%t [UART Sequencer] End", $time);
  endtask : run

endclass : uart_sequencer

`endif  // UART_SEQUENCER_SV
