/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : avalon_transaction.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the definition of the Avalon possible
              transaction

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/

`ifndef AVALON_TRANSACTION_SV
`define AVALON_TRANSACTION_SV

typedef enum {
  UART_SEND,
  UART_READ,
  SET_CLK_PER_BIT,
  ASSERT_TX_FIFO_EMPTY,
  ASSERT_RX_FIFO_FULL,
  ASSERT_RX_FIFO_EMPTY,
  ASSERT_RX_FIFO_NOT_EMPTY,
  ASSERT_TX_FIFO_FULL,
  ASSERT_TX_FIFO_NOT_EMPTY,
  ASSERT_CLK_PER_BIT,
  UART_READ_UNTIL_EMPTY
} avalon_transaction_type_t;

class avalon_transaction #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  avalon_transaction_type_t transaction_type;
  rand logic [31:0] data;
  logic [31:0] clk_to_wait_before_transaction;

  function automatic int max_value();
    return (2 ** DATASIZE) - 1;
  endfunction

  covergroup cov_group;
    cov_data: coverpoint data[DATASIZE-1:0] {
      bins petit = {[0 : max_value() / 4]};
      bins grand = {[max_value() - (max_value() / 4) : max_value()]};
      bins all_values[DATASIZE] = {[max_value() / 4 + 1 : max_value() - (max_value() / 4) - 1]};
    }
  endgroup

  function new;
    clk_to_wait_before_transaction = 0;
    cov_group = new;
  endfunction

endclass : avalon_transaction


typedef mailbox#(avalon_transaction) avalon_fifo_t;

`endif  // AVALON_TRANSACTION_SV
