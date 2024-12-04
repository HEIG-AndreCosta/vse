/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : avalon_sequencer.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the sequencer responsible for generating the
              data to test the UART on the Avalon side

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/

`ifndef AVALON_SEQUENCER_SV
`define AVALON_SEQUENCER_SV

class avalon_sequencer #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  int testcase;
  avalon_fifo_t sequencer_to_driver_fifo;

  const int DEFAULT_CLK = 20;
  const logic [31:0] DEFAULT_CLK_PER_BIT = (1_000_000_000 / 9600) / DEFAULT_CLK;  //9600 baudrate
  const logic [31:0] DEFAULT_TIME_TO_SEND = (DEFAULT_CLK_PER_BIT * DEFAULT_CLK) * 2;
  task run_all_scenarios;
    test_write;
    test_read;
    test_fifo_empty;
    test_fifo_full;
    test_rx_fifo_full;
    test_boundaries;
    test_correct_clk_per_bit;
  endtask

  // Utility function that sets the nb of clk per bit on the duv side by
  // sending the corresponding avl transaction to the driver
  task set_clk_per_bit(logic [31:0] clk_per_bit);
    automatic avalon_transaction trans = new;
    trans.transaction_type = SET_CLK_PER_BIT;
    trans.data = clk_per_bit;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Test write
  // Tests the fact that we can send a payload and it its correctly received
  // on the other side
  // It also asserts the TX_FIFO empty flag on the status register
  task test_write();
    automatic avalon_transaction trans;

    trans = new;
    trans.transaction_type = ASSERT_TX_FIFO_EMPTY;
    sequencer_to_driver_fifo.put(trans);

    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans = new;
    trans.transaction_type = UART_SEND;
    trans.data = 32'h12345;
    sequencer_to_driver_fifo.put(trans);

    trans = new;
    trans.transaction_type = ASSERT_TX_FIFO_NOT_EMPTY;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Test write boundaries
  // Tests the fact that we can send a payload full of zeros or full of ones
  // and they're correctly received on the other side
  // It also asserts the TX_FIFO empty flag on the status register
  task test_boundaries;
    automatic avalon_transaction trans;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans = new;
    trans.transaction_type = ASSERT_TX_FIFO_EMPTY;
    sequencer_to_driver_fifo.put(trans);

    // Data = 0xfffff
    trans = new;
    trans.transaction_type = UART_SEND;
    trans.data = -1;
    sequencer_to_driver_fifo.put(trans);

    trans = new;
    trans.transaction_type = ASSERT_TX_FIFO_NOT_EMPTY;
    sequencer_to_driver_fifo.put(trans);

    // Data = 0
    trans = new;
    trans.transaction_type = UART_SEND;
    trans.data = 0;
    sequencer_to_driver_fifo.put(trans);

    trans = new;
    trans.transaction_type = ASSERT_TX_FIFO_NOT_EMPTY;
    sequencer_to_driver_fifo.put(trans);

    // On the other end, uart also sent us data
    read_with_delay_between(2, DEFAULT_TIME_TO_SEND);
  endtask

  // Test read
  // Tests the fact that we can received a payload from the uart
  // It also asserts the RX_FIFO empty flag on the status register
  task test_read;
    automatic avalon_transaction trans;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans = new;
    trans.transaction_type = ASSERT_RX_FIFO_EMPTY;
    sequencer_to_driver_fifo.put(trans);

    trans = new;
    trans.transaction_type = ASSERT_RX_FIFO_NOT_EMPTY;
    trans.clk_to_wait_before_transaction = DEFAULT_TIME_TO_SEND;
    sequencer_to_driver_fifo.put(trans);

    trans = new;
    trans.transaction_type = UART_READ;
    trans.clk_to_wait_before_transaction = 0;
    sequencer_to_driver_fifo.put(trans);

    trans = new;
    trans.transaction_type = ASSERT_RX_FIFO_EMPTY;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Test fifo empty
  // Check that the status register shows both fifos as empty at the start
  task test_fifo_empty;
    automatic avalon_transaction trans = new;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans.transaction_type = ASSERT_TX_FIFO_EMPTY;
    sequencer_to_driver_fifo.put(trans);
    trans = new;
    trans.transaction_type = ASSERT_RX_FIFO_EMPTY;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Test fifo full
  // Check that the status register indicates the tx fifo is full if we send
  // enough data
  task test_fifo_full;
    automatic avalon_transaction trans;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    for (int i = 0; i < FIFOSIZE + 1; ++i) begin
      trans = new;
      trans.transaction_type = UART_SEND;
      trans.data = i;
      sequencer_to_driver_fifo.put(trans);
    end
    trans = new;
    trans.transaction_type = ASSERT_TX_FIFO_FULL;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Test rx fifo full
  // Check that the status register indicates the rx fifo is full if we
  // receive enough data
  task test_rx_fifo_full;
    automatic avalon_transaction trans;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans = new;
    trans.transaction_type = ASSERT_RX_FIFO_FULL;
    trans.clk_to_wait_before_transaction = DEFAULT_CLK_PER_BIT * 20 * (FIFOSIZE + 1);
    sequencer_to_driver_fifo.put(trans);

    read_with_delay_between(FIFOSIZE, 0);
  endtask

  // Tests that we read the same value in the clk per bit register we put
  // before
  // Check that the status register indicates the rx fifo is full if we
  // receive enough data
  task test_correct_clk_per_bit;
    automatic avalon_transaction trans;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);

    trans = new;
    trans.transaction_type = ASSERT_CLK_PER_BIT;
    trans.data = DEFAULT_CLK_PER_BIT;
    sequencer_to_driver_fifo.put(trans);
  endtask

  // Utility task that send multiple read transaction to the driver
  task read_with_delay_between(int nb_reads, logic [31:0] delay);
    automatic avalon_transaction trans;
    for (int i = 0; i < nb_reads; ++i) begin
      trans = new;
      trans.transaction_type = UART_READ;
      trans.clk_to_wait_before_transaction = delay;
      sequencer_to_driver_fifo.put(trans);
    end
  endtask

  // Test what happens if the baudrate is too high
  // This test should not be run automatically but it may be useful to know
  // what happens if the other device isn't set with the correct baudrate
  task test_baudrate_too_high;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    read_with_delay_between(FIFOSIZE * 10, DEFAULT_TIME_TO_SEND);
  endtask

  // Test what happens if the baudrate is too low
  // This test should not be run automatically but it may be useful to know
  // what happens if the other device isn't set with the correct baudrate
  task test_baudrate_too_low;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    read_with_delay_between(FIFOSIZE * 10, DEFAULT_TIME_TO_SEND);
  endtask

  task run;
    $display("%t [AVL Sequencer] Testcase %d", $time, testcase);
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
    $display("%t [AVL Sequencer] End", $time);
  endtask : run

endclass : avalon_sequencer

`endif  // AVALON_SEQUENCER_SV
