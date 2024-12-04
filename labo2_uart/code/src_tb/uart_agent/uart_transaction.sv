/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : uart_transaction.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the definition of the UART in terms of
              a transaction.

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/

`ifndef UART_TRANSACTION_SV
`define UART_TRANSACTION_SV

typedef enum {
  UART_RX_DUV_TX,
  UART_TX_DUV_RX,
  UART_TX_DUV_RX_MODIFY_BAUDRATE,
  UART_WAIT
} uart_transaction_type_t;

class uart_transaction #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  uart_transaction_type_t transaction_type;
  rand logic [DATASIZE-1:0] data;

  //By default the driver will use the correct baudrate
  // but in case the transaction is of type XXX_MODIFY_BAUDRATE
  // the driver will used the baudrate defined here
  logic [DATASIZE-1:0] baudrate;

  function automatic int max_value();
    return (2 ** DATASIZE) - 1;
  endfunction

  covergroup cov_group;
    cov_data: coverpoint data {
      bins petit = {[0 : max_value() / 4]};
      bins grand = {[max_value() - (max_value() / 4) : max_value()]};
      bins all_values[DATASIZE] = {[max_value() / 4 + 1 : max_value() - (max_value() / 4) - 1]};
    }
  endgroup

  function new;
    cov_group = new;
  endfunction

endclass : uart_transaction


typedef mailbox#(uart_transaction) uart_fifo_t;

`endif  // UART_TRANSACTION_SV
