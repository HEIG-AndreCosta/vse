/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : uart_driver.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the monitor observing the UART interface

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/

`ifndef UART_MONITOR_SV
`define UART_MONITOR_SV

import objections_pkg::*;

class uart_monitor #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  int testcase;

  int ns_per_bit;

  uart_fifo_t uart_to_scoreboard_tx_fifo;

  virtual uart_itf vif;

  task run;
    $display("%t [UART Monitor] Start", $time);

    #20;

    while (1) begin
      uart_transaction #(DATASIZE, FIFOSIZE) transaction;
      @(negedge vif.tx_o);
      objections_pkg::objection::get_inst().raise();
      $display("%t [UART Monitor] Detected Start Condition", $time);
      transaction = new;
      transaction.transaction_type = UART_RX_DUV_TX;
      #(ns_per_bit + (ns_per_bit / 2));
      for (int i = DATASIZE; i > 0; i--) begin
        transaction.data[i-1] = vif.tx_o;
        #ns_per_bit;
      end
      uart_to_scoreboard_tx_fifo.put(transaction);
      objections_pkg::objection::get_inst().drop();
    end
  endtask : run


endclass : uart_monitor

`endif  // UART_MONITOR_SV
