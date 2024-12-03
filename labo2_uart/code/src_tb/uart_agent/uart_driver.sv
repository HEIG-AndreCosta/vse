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
Description : This file contains the driver representing the UART remote host

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/


`ifndef UART_DRIVER_SV
`define UART_DRIVER_SV

import objections_pkg::*;

class uart_driver #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  int testcase;

  int ns_per_bit;

  uart_fifo_t sequencer_to_driver_fifo;
  uart_fifo_t uart_to_scoreboard_rx_fifo;

  virtual uart_itf vif;

  task run;
    int test_ns_per_bit;
    automatic uart_transaction transaction;
    $display("%t [UART Driver] Start", $time);
    $display("%t [UART Driver] ns_per_bit %d", $time, ns_per_bit);

    vif.rx_i = 1;
    // Allow setup of the DUV baudrate
    #1000;

    while (1) begin
      sequencer_to_driver_fifo.get(transaction);
      objections_pkg::objection::get_inst().raise();
      if (transaction.transaction_type == UART_WAIT) begin
        #transaction.data;
        objections_pkg::objection::get_inst().drop();
        continue;
      end else if (transaction.transaction_type == UART_TX_DUV_RX_MODIFY_BAUDRATE) begin
        test_ns_per_bit = 1_000_000_000 / transaction.baudrate;
        $display("%t [UART Driver] Sending with new baudrate. Baudrate: %d, ns_per_bit: %d", $time,
                 transaction.baudrate, test_ns_per_bit);
      end else begin
        test_ns_per_bit = ns_per_bit;
      end
      #test_ns_per_bit;
      // Start Bit
      vif.rx_i = 0;
      #test_ns_per_bit;
      for (int i = DATASIZE; i > 0; i--) begin
        vif.rx_i = transaction.data[i-1];
        #test_ns_per_bit;
      end
      // Stop Bit
      vif.rx_i = 1;
      $display("%t [UART Driver] Sent data %x", $time, transaction.data);
      uart_to_scoreboard_rx_fifo.put(transaction);
      objections_pkg::objection::get_inst().drop();
    end

    $display("%t [UART Driver] End", $time);
  endtask : run

endclass : uart_driver

`endif  // UART_DRIVER_SV
