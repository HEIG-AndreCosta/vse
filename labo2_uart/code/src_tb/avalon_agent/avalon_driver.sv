/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : avalon_driver.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the driver representing the avalon access
              behavior

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/


`ifndef AVALON_DRIVER_SV
`define AVALON_DRIVER_SV

import objections_pkg::*;

class avalon_driver #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  int testcase;

  avalon_fifo_t sequencer_to_driver_fifo;
  avalon_fifo_t avalon_to_scoreboard_rx_fifo;
  avalon_fifo_t avalon_to_scoreboard_tx_fifo;

  virtual avalon_itf vif;

  task send_to_scoreboard(avl_transaction transaction);
    if (transaction.write_i == 1) begin
      $display("%t [AVL Driver] Sending write transaction to scoreboard", $time);
      driver_to_scoreboard_tx_fifo.put(transaction);
    end else begin
      $display("%t [AVL Driver] Sending read transaction to scoreboard", $time);
      driver_to_scoreboard_rx_fifo.put(transaction);
    end
  endtask : send_to_scoreboard

  function void write(avalon_itf vif, avl_transaction transaction);
    vif.address_i = transaction.address;
    vif.write_i = transaction.is_write;
    vif.read_i = !transaction.is_write;
    vif.writedata_i = transaction.data;
  endfunction

  task automatic get_status(avalon_itf vif, output logic [3:0] status);
    vif.address_i = 0;
    vif.write_i = 0;
    vif.read_i = 1;
    do begin
      @(posedge vif.clk_i);
    end while (vif.readdatavalid_i == 0);

    status = vif.readdata_i;
  endtask : get_status

  function bool send_buffer_is_full;
    vif.read_i = 1;
    vif.write_i = 0;
    vif.address_i = 0;

  endfunction : send_buffer_is_full

  task run;
    automatic avalon_transaction transaction;
    automatic int i = 0;
    $display("%t [AVL Driver] Start", $time);

    vif.rst_i = 1;
    vif.address_i = 0;
    vif.byteenable_i = 'hf;
    vif.write_i = 0;
    vif.writedata_i = 0;
    vif.read_i = 0;

    @(posedge vif.clk_i);
    vif.rst_i <= 0;
    @(posedge vif.clk_i);
    @(posedge vif.clk_i);
    while (1) begin
      sequencer_to_driver_fifo.get(transaction);
      @(posedge vif.clk_i) begin
        send_to_scoreboard(transaction);
        write(vif, transaction);
      end
      @(negedge vif.clk_i);
    end

  endtask : run

endclass : avalon_driver

`endif  // AVALON_DRIVER_SV
