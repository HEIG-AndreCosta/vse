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
    automatic uart_transaction transaction;
    $display("%t [UART Driver] Start", $time);
    $display("%t [UART Driver] ns_per_bit %d", $time, ns_per_bit);

    vif.rx_i = 1;
    // Allow setup of the DUV baudrate
    #1000;

    while (1) begin
      automatic logic [DATASIZE:0] data = 0;

      sequencer_to_driver_fifo.get(transaction);
      objections_pkg::objection::get_inst().raise();

      data[0] = 0;
      for (int i = 1; i < DATASIZE + 1; i++) begin
        data[i] = transaction.data[i-1];
      end
      for (int i = 0; i < DATASIZE + 1; i++) begin
        vif.rx_i = data[i];
        #ns_per_bit;
      end
      vif.rx_i = 1;
      $display("%t [UART Driver] Sent data %x", $time, data);
      uart_to_scoreboard_rx_fifo.put(transaction);
      objections_pkg::objection::get_inst().drop();
    end

    $display("%t [UART Driver] End", $time);
  endtask : run

endclass : uart_driver

`endif  // UART_DRIVER_SV
