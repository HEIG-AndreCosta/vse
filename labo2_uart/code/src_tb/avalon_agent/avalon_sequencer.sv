/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Business and Engineering in Canton de Vaud
********************************************************************************
REDS
Institute Reconfigurable Embedded Digital Systems
********************************************************************************

File     : avalon_sequencer.sv
Author   : Clément Dieperink
Date     : 15.10.2024

Context  : Lab for the verification of an UART

********************************************************************************
Description : This file contains the sequencer responsible for generating the
              data to test the UART on the Avalon side

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   15.10.2024  CDK        Initial version

*******************************************************************************/

`ifndef AVALON_SEQUENCER_SV
`define AVALON_SEQUENCER_SV

class simple_sequencer extends avalon_sequencer;
  rand logic [DATASIZE - 1:0] data;

  function new;
    $display("%t [AVL simple_sequencer] Created", $time);
    assert (!this.randomize());
  endfunction : new

  task run;
    automatic avalon_transaction transaction;
    $display("%t [AVL simple_sequencer] Start", $time);
    transaction.data = data;
    sequencer_to_driver_fifo.put(transaction);
    $display("%t [AVL simple_sequencer] End", $time);
  endtask : run

endclass : simple_sequencer

class avalon_sequencer #(
    int DATASIZE = 20,
    int FIFOSIZE = 10
);

  int testcase;

  task all_sequencers;
    simple_sequencer simple_sequencer;
    simple_sequencer.run;
  endtask : all_sequencers

  task play_sequencers;

    case (testcase)
      0: begin
        all_sequencers;
      end
      1: begin
        simple_sequencer simple_sequencer;
        simple_sequencer.run;
      end
      default: begin
        $display("%t [AVL Sequencer] Testcase %d not implemented", $time, testcase);
      end
    endcase
  endtask : play_sequencers

  avalon_fifo_t sequencer_to_driver_fifo;

  task run;
    $display("%t [AVL Sequencer] Testcase %d", $time, testcase);
    play_sequencers;
    $display("%t [AVL Sequencer] End", $time);
  endtask : run

endclass : avalon_sequencer

`endif  // AVALON_SEQUENCER_SV
