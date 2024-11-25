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

    vif.rx_i = 1;
    // Allow setup of the DUV baudrate
    #1000;

    while (1) begin
      automatic logic [DATASIZE:0] data = 0;

      sequencer_to_driver_fifo.get(transaction);

      data[0] = 0;
      //TODO : faire une boucle for pour faire la copie de transaction.data
      //dans data
      //data[1:DATASIZE] = transaction.data;
      for (int i = 0; i < DATASIZE; i++) begin
        #ns_per_bit;
        vif.rx_i = data[i];
      end
      vif.rx_i = 1;
      $display("%t [UART Driver] Sended data %h", $time, data);
      uart_to_scoreboard_rx_fifo.put(transaction);
    end

    $display("%t [UART Driver] End", $time);
  endtask : run

endclass : uart_driver

`endif  // UART_DRIVER_SV
