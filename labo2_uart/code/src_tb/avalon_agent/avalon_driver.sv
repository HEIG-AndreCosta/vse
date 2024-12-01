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


  task wait_ready();
    while (vif.waitrequest_o) begin
      @(posedge vif.clk_i);
    end
  endtask

  task wait_nb_clks(int nb_clks);
    automatic int i;
    $display("%t [AVL Driver] Waiting %d", $time, nb_clks);
    for (i = 0; i < nb_clks; ++i) begin
      @(posedge vif.clk_i);
    end
  endtask

  task do_read(logic [13:0] address);
    vif.address_i = address;
    vif.write_i = 0;
    vif.read_i = 1;
    do begin
      @(posedge vif.clk_i);
      vif.read_i = 0;
    end while (!vif.readdatavalid_o);
    $display("%t [AVL Driver] Do Read %d %x", $time, address, vif.readdata_o);
  endtask
  task do_write(logic [13:0] address, logic [31:0] data);
    wait_ready;
    $display("%t [AVL Driver] Do Write %d %x", $time, address, data);
    vif.address_i = address;
    vif.write_i = 1;
    vif.read_i = 0;
    vif.writedata_i = data;
    @(posedge vif.clk_i);
    wait_ready;
    vif.write_i = 0;
  endtask

  task read_status_register();
    do_read(0);
  endtask

  task send_tx_data(logic [31:0] data);
    do_write(1, data);
  endtask

  task read_rx_data();
    do_read(2);
  endtask

  task set_clk_per_bit(logic [31:0] clk_per_bit);
    do_write(3, clk_per_bit);
  endtask
  task assert_fifo_rx_not_empty();
    automatic logic [31:0] status;
    read_status_register;
    status = vif.readdata_o;
    assert (status & 32'h4);
  endtask

  task do_transaction(avalon_transaction transaction);
    automatic logic [31:0] status;
    $display("%t [AVL Driver] Do Transaction %d", $time, transaction.transaction_type);
    case (transaction.transaction_type)
      UART_SEND: begin
        send_tx_data(transaction.data);
        avalon_to_scoreboard_tx_fifo.put(transaction);
      end
      UART_READ: begin
        wait_nb_clks(transaction.clk_to_wait_before_read);
        assert_fifo_rx_not_empty;
        read_rx_data;
        transaction.data = vif.readdata_o;
        avalon_to_scoreboard_rx_fifo.put(transaction);
      end
      ASSERT_TX_FIFO_EMPTY: begin
        read_status_register;
        status = vif.readdata_o;
        assert (!(status & 32'h1));
        assert (status & 32'h8);
      end
      ASSERT_RX_FIFO_FULL: begin
        wait_nb_clks(transaction.clk_to_wait_before_read);
        read_status_register;
        status = vif.readdata_o;
        assert (status & 32'h2);
        assert (status & 32'h4);
      end
      ASSERT_RX_FIFO_HAS_DATA: begin
        assert_fifo_rx_not_empty;
      end
      ASSERT_RX_FIFO_EMPTY: begin
        read_status_register;
        status = vif.readdata_o;
        assert (!(status & 32'h2));
        assert (!(status & 32'h4));
      end
      ASSERT_TX_FIFO_FULL: begin
        read_status_register;
        status = vif.readdata_o;
        assert (status & 32'h1);
        assert (!(status & 32'h8));
      end
      SET_CLK_PER_BIT: begin
        set_clk_per_bit(transaction.data);
      end
      default: begin
      end  //should never get here
    endcase
  endtask

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
      @(posedge vif.clk_i);
      sequencer_to_driver_fifo.get(transaction);
      objections_pkg::objection::get_inst().raise();
      do_transaction(transaction);
      objections_pkg::objection::get_inst().drop();
    end

  endtask : run

endclass : avalon_driver

`endif  // AVALON_DRIVER_SV
