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
  ASSERT_RX_FIFO_HAS_DATA,
  ASSERT_RX_FIFO_EMPTY,
  ASSERT_TX_FIFO_FULL
} avalon_transaction_type_t;

class avalon_transaction #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  avalon_transaction_type_t transaction_type;
  logic [31:0] data;

endclass : avalon_transaction


typedef mailbox#(avalon_transaction) avalon_fifo_t;

`endif  // AVALON_TRANSACTION_SV
