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

  const logic [31:0] DEFAULT_CLK_PER_BIT = 10;  //10_416_700;  //9600 baudrate with 10 ns clock
  task run_all_scenarios;
    test_write;
    test_read;
    test_fifo_empty;
    test_fifo_full;
  endtask

  task set_clk_per_bit(logic [31:0] clk_per_bit);
    automatic avalon_transaction trans = new;
    trans.transaction_type = SET_CLK_PER_BIT;
    trans.data = clk_per_bit;
    sequencer_to_driver_fifo.put(trans);
  endtask
  task test_write();
    automatic avalon_transaction trans = new;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans.transaction_type = UART_SEND;
    trans.data = 32'hcafe4321;
    sequencer_to_driver_fifo.put(trans);
  endtask

  task test_read;
    automatic avalon_transaction trans = new;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans.transaction_type = UART_READ;
    sequencer_to_driver_fifo.put(trans);
  endtask

  task test_fifo_empty;
    automatic avalon_transaction trans = new;
    set_clk_per_bit(DEFAULT_CLK_PER_BIT);
    trans.transaction_type = ASSERT_TX_FIFO_EMPTY;
    sequencer_to_driver_fifo.put(trans);
  endtask

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


  task run;
    $display("%t [AVL Sequencer] Testcase %d", $time, testcase);
    case (testcase)
      0: run_all_scenarios;
      1: test_write;
      2: test_read;
      3: test_fifo_empty;
      4: test_fifo_full;
      default: $display("Invalid test case %d", testcase);
    endcase
    $display("%t [AVL Sequencer] End", $time);
  endtask : run

endclass : avalon_sequencer

`endif  // AVALON_SEQUENCER_SV
