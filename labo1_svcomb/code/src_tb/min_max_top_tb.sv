/*******************************************************************************
HEIG-VD
Haute Ecole d'Ingenerie et de Gestion du Canton de Vaud
School of Engineering and Management Vaud
********************************************************************************
REDS Institute
Reconfigurable and Embedded Digital Systems
********************************************************************************

File     : min_max_top_tb.sv
Author   : Yann Thoma
Date     : 07.10.2024

Context  : min max component testbench

********************************************************************************
Description : This testbench is decomposed into stimuli
              generation and verification, with the use of interfaces.

********************************************************************************
Dependencies : -

********************************************************************************
Modifications :
Ver   Date        Person     Comments
1.0   07.10.2024  YTA        Initial version

*******************************************************************************/


interface min_max_in_itf #(
    int VALSIZE
);
  logic [1:0] com;
  logic [VALSIZE-1:0] max;
  logic [VALSIZE-1:0] min;
  logic osci;
  logic [VALSIZE-1:0] value;
endinterface

interface min_max_out_itf #(
    int VALSIZE
);
  logic [2**VALSIZE-1:0] leds;
endinterface

module min_max_top_tb #(
    int VALSIZE,
    int TESTCASE,
    int ERRNO
);

  timeunit 1ns;  // Definition of the time unit
  timeprecision 1ns;  // Definition of the time precision

  // Reference
  logic [2**VALSIZE-1:0] leds_ref;

  int nb_errors = 0;

  // Timings definitions
  time sim_step = 10ns;
  time pulse = 0ns;

  logic error_signal = 0;

  logic synchro = 0;

  always #(sim_step / 2) synchro = ~synchro;

  min_max_in_itf input_itf ();
  min_max_out_itf output_itf ();

  typedef logic [VALSIZE-1:0] input_t;
  typedef logic [2**VALSIZE-1:0] output_t;

  class Input;
    logic [1:0] com;

    rand logic [VALSIZE-1:0] max;
    rand logic [VALSIZE-1:0] min;
    rand logic [VALSIZE-1:0] value;
    logic osci;

    constraint max_bigger_than_min_c {max > min;}
    constraint value_bigger_than_max_c {value > max;}
    constraint value_smaller_than_min_c {value < min;}
    constraint value_between_max_and_min_c {value <= max && value >= min;}

    covergroup cov_group;
      cov_max: coverpoint max {
        option.auto_bin_max = 1000;
        bins petit = {[0 : 10]};
        bins grand = {[(2 ** VALSIZE) - 10 : (2 ** VALSIZE) - 1]};

      }
      cov_min: coverpoint min {
        option.auto_bin_max = 1000;
        bins petit = {[0 : 10]};
        bins grand = {[(2 ** VALSIZE) - 10 : (2 ** VALSIZE) - 1]};
      }
      cov_val: coverpoint value {
        option.auto_bin_max = 1000;
        bins petit = {[0 : 10]};
        bins grand = {[(2 ** VALSIZE) - 10 : (2 ** VALSIZE) - 1]};
      }
    endgroup
    function new();
      cov_group = new;
    endfunction
    //function void post_randomize();
    //endfunction
  endclass


  // DUV instantiation
  min_max_top #(VALSIZE, ERRNO) duv (
      .com_i (input_itf.com),
      .max_i (input_itf.max),
      .min_i (input_itf.min),
      .osc_i (input_itf.osci),
      .val_i (input_itf.value),
      .leds_o(output_itf.leds)
  );

  function automatic random_or_fatal(Input obj);
    assert (obj.randomize())
    else $fatal("No solutions for obj.randomize");
  endfunction

  function automatic map_obj_to_input_itf(Input obj);
    input_itf.com   = obj.com;
    input_itf.osci  = obj.osci;
    input_itf.min   = obj.min;
    input_itf.max   = obj.max;
    input_itf.value = obj.value;
  endfunction

  task automatic test_both_osci_state();
    input_itf.osci = 0;
    compute_reference(input_itf.com, input_itf.min, input_itf.max, input_itf.value, input_itf.osci,
                      leds_ref);
    @(posedge (synchro));
    input_itf.osci = 1;
    compute_reference(input_itf.com, input_itf.min, input_itf.max, input_itf.value, input_itf.osci,
                      leds_ref);
    @(posedge (synchro));
  endtask

  task automatic test_marche_normale_values_between_min_and_max;
    Input obj;
    obj = new;
    obj.com = 0;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(1);

    $display("Running Test Marche Normale Between Min and Max");
    while (obj.cov_group.get_inst_coverage() < 100) begin
      random_or_fatal(obj);
      obj.cov_group.sample();
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_marche_normale_values_bigger_than_max;
    Input obj;
    obj = new;
    obj.com = 0;
    obj.value_bigger_than_max_c.constraint_mode(1);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Marche Normale Val > Max");
    while (obj.cov_group.get_inst_coverage() < 100) begin
      random_or_fatal(obj);
      obj.cov_group.sample();
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_marche_normale_values_less_than_min;
    Input obj;
    obj = new;
    obj.com = 0;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(1);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Marche Normale Val < Min");
    while (obj.cov_group.get_inst_coverage() < 100) begin
      random_or_fatal(obj);
      obj.cov_group.sample();
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_val_lineaire;
    Input obj;
    obj = new;
    obj.com = 1;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Value Lineaire");
    while (obj.cov_group.cov_val.get_inst_coverage() < 100) begin
      random_or_fatal(obj);
      obj.cov_group.sample();
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_eteint;
    Input obj;
    obj = new;
    obj.com = 2;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Eteint");
    while (obj.cov_group.cov_val.get_inst_coverage() < 100) begin
      random_or_fatal(obj);
      obj.cov_group.sample();
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_allume_fort;
    Input obj;
    obj = new;
    obj.com = 3;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Allume fort");
    while (obj.cov_group.cov_val.get_inst_coverage() < 100) begin
      random_or_fatal(obj);
      obj.cov_group.sample();
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic run_all_scenarios;
    test_eteint;
    test_allume_fort;
    test_val_lineaire;
    test_marche_normale_values_between_min_and_max;
    test_marche_normale_values_less_than_min;
    test_marche_normale_values_bigger_than_max;
  endtask

  task automatic test_scenario;

    case (TESTCASE)
      0: run_all_scenarios;
      1: test_eteint;
      2: test_allume_fort;
      3: test_val_lineaire;
      4: test_marche_normale_values_between_min_and_max;
      5: test_marche_normale_values_less_than_min;
      6: test_marche_normale_values_bigger_than_max;
      default: $diplay("Invalid test case %d", TESTCASE);
    endcase

  endtask

  task automatic compute_reference(logic [1:0] com, input_t min, input_t max, input_t value,
                                   logic osci, output output_t leds);

    case (com)
      0: begin
        if (value < min || value > max) begin
          leds = 0;
        end else begin
          for (int i = 0; i < min; ++i) begin
            leds[i] = 0;
          end
          for (int i = min; i <= value; ++i) begin
            leds[i] = 1'b1;
          end
          for (int i = value + 1; i <= max; ++i) begin
            leds[i] = osci;
          end
          for (int i = max + 1; i < VALSIZE; ++i) begin
            leds[i] = 0;
          end
        end
      end
      1: begin
        for (int i = 0; i <= value; ++i) begin
          leds[i] = 1'b1;
        end
      end
      2: leds = 0;
      3: leds = 1;
      default: ;
    endcase


  endtask

  task automatic compute_reference_task;
    forever begin
      @(posedge (synchro));
      #1;
      compute_reference(input_itf.com, input_itf.min, input_itf.max, input_itf.value,
                        input_itf.osci, leds_ref);
    end
  endtask

  task automatic verification;
    @(negedge (synchro));
    forever begin
      if (output_itf.leds != leds_ref) begin
        nb_errors++;
        if (ERRNO <= 3) begin
          $display(
              "Error for input: com = %d osci = %d val_i = %d max_i = %d min_i %d. Expected: %d, Observed: %d",
              input_itf.com, input_itf.osci, input_itf.value, input_itf.max, input_itf.min,
              leds_ref, output_itf.leds);
          error_signal = 1;
          #pulse;
          error_signal = 0;
        end
      end
      @(negedge (synchro));
    end
  endtask

  initial begin

    $display("Starting simulation");
    fork
      test_scenario;
      compute_reference_task;
      verification;
    join_any

    $display("Ending simulation");
    if (nb_errors > 0) begin
      if (ERRNO > 3) begin
        $display("OK Detected %d with errno: %d.", nb_errors, ERRNO);
      end else begin
        $display("ERROR %d errors detected.", nb_errors, ERRNO);
      end
    end else begin
      if (ERRNO > 3) begin
        $display("ERROR. Bad TB. 0 errors detected with ERRNO > 3 (%d).", ERRNO);
      end else begin
        $display("OK No errors detected.");
      end
    end


    $finish;
  end

endmodule
