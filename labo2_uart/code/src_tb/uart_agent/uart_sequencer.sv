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
  endtask

  task test_write();
  endtask

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

  task test_read;
    automatic uart_transaction trans = new;
    trans.transaction_type = UART_TX_DUV_RX;
    trans.data = 20'h12345;
    sequencer_to_driver_fifo.put(trans);
  endtask

  task test_fifo_empty;
  endtask

  task test_fifo_full;
  endtask

  task test_correct_clk_per_bit;
  endtask

  task test_rx_fifo_full;
    for (int i = 0; i < FIFOSIZE; ++i) begin
      automatic uart_transaction trans = new;
      trans.transaction_type = UART_TX_DUV_RX;
      trans.data = i;
      sequencer_to_driver_fifo.put(trans);
    end
  endtask

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
      // Baudrate tests are not run automatically since they are expected to
      // generate errors. They exist to be run manually and checked by
      // a human.
      8: test_baudrate_too_high;
      9: test_baudrate_too_low;

      default: $display("Invalid test case %d", testcase);
    endcase
    $display("%t [UART Sequencer] End", $time);
  endtask : run

endclass : uart_sequencer

`endif  // UART_SEQUENCER_SV
