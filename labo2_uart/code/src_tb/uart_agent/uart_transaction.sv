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
  logic [DATASIZE-1:0] data;

  //By default the driver will use the correct baudrate
  // but in case the transaction is of type XXX_MODIFY_BAUDRATE
  // the driver will used the defined baudrate
  logic [DATASIZE-1:0] baudrate;

endclass : uart_transaction


typedef mailbox#(uart_transaction) uart_fifo_t;

`endif  // UART_TRANSACTION_SV
