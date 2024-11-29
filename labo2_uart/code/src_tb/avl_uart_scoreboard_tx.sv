/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : avl_uart_scoreboard_tx.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the scoreboard responsible for comparing the
              input/output transactions for TX

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/

`ifndef UART_TRANSCEIVER_SCOREBOARD_TX_SV
`define UART_TRANSCEIVER_SCOREBOARD_TX_SV

class avl_uart_scoreboard_tx #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  int testcase;

  logic waiting_uart_trans = 0;

  int nb_transactions = 0;
  int nb_errors = 0;
  avalon_fifo_t avalon_to_scoreboard_tx_fifo;
  uart_fifo_t uart_to_scoreboard_tx_fifo;

  task end_display;
    $display("%t [Scoreboard TX] Transactions: %d Errors: %d Waiting Uart Transaction: %d", $time,
             nb_transactions, nb_errors, waiting_uart_trans);
  endtask : end_display

  task run;
    automatic avalon_transaction avalon_trans;
    automatic uart_transaction uart_trans;
    automatic int i;
    automatic logic [DATASIZE -1:0] expected;

    $display("%t [Scoreboard TX] Start", $time);

    while (1) begin
      objections_pkg::objection::get_inst().drop();
      avalon_to_scoreboard_tx_fifo.get(avalon_trans);
      waiting_uart_trans = 1;
      uart_to_scoreboard_tx_fifo.get(uart_trans);
      objections_pkg::objection::get_inst().raise();
      waiting_uart_trans = 0;
      assert (uart_trans.transaction_type == TX);
      assert (avalon_trans.transaction_type == UART_SEND);

      for (int i = 0; i < DATASIZE; ++i) begin

        expected[i] = avalon_trans.data[i];
      end
      nb_transactions++;
      if (expected != uart_trans.data) begin
        nb_errors++;
        $error("Wrong Tx Data Expected: %x Got: %x", expected, uart_trans.data);
      end
    end
    $display("%t [Scoreboard TX] End", $time);
  endtask : run

endclass : avl_uart_scoreboard_tx

`endif  // UART_TRANSCEIVER_SCOREBOARD_TX_SV
