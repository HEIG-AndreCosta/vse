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

  function automatic int max_value();
    return (2 ** VALSIZE) - 1;
  endfunction

  function automatic int nb_iterations();
    int max = max_value();
    if (max > 1000) begin
      return 1000;
    end
    return max;
  endfunction

  class Input;
    rand logic [1:0] com;

    rand logic [VALSIZE-1:0] max;
    rand logic [VALSIZE-1:0] min;
    rand logic [VALSIZE-1:0] value;
    logic osci;

    constraint com_distribution_c {
      com dist {
        0 := 7,
        1 := 1,
        2 := 1,
        3 := 1
      };
    }

    constraint max_bigger_than_min_c {max > min;}
    constraint value_bigger_than_max_c {value > max;}
    constraint value_smaller_than_min_c {value < min;}
    constraint value_between_max_and_min_c {value <= max && value >= min;}
    constraint order_max_c {solve max before min;}
    constraint order_value_c {solve max, min before value;}

    covergroup cov_group;
      option.auto_bin_max = 1000;
      cov_com: coverpoint com;
      cov_max: coverpoint max {
        option.auto_bin_max = 1000;
        bins petit = {[0 : max_value() / 4]};
        bins grand = {[max_value() - (max_value() / 4) : max_value()]};
        bins all_values[VALSIZE] = {[max_value() / 4 + 1 : max_value() - (max_value() / 4) - 1]};
      }
      cov_min: coverpoint min {
        option.auto_bin_max = 1000;
        bins petit = {[0 : max_value() / 4]};
        bins grand = {[max_value() - (max_value() / 4) : max_value()]};
        bins all_values[VALSIZE] = {[max_value() / 4 + 1 : max_value() - (max_value() / 4) - 1]};
      }
      cov_val: coverpoint value {
        option.auto_bin_max = 1000;
        bins petit = {[0 : max_value() / 4]};
        bins grand = {[max_value() - (max_value() / 4) : max_value()]};
        bins all_values[VALSIZE] = {[max_value() / 4 + 1 : max_value() - (max_value() / 4) - 1]};
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

  function automatic void random_or_fatal(Input obj);
    assert (obj.randomize())
    else $fatal("No solutions for obj.randomize");
  endfunction

  function automatic void map_obj_to_input_itf(Input obj);
    input_itf.com   = obj.com;
    input_itf.osci  = obj.osci;
    input_itf.min   = obj.min;
    input_itf.max   = obj.max;
    input_itf.value = obj.value;
  endfunction


  task automatic test_both_osci_state();
    input_itf.osci = 0;
    @(posedge (synchro));
    input_itf.osci = 1;
    @(posedge (synchro));
  endtask

  task automatic test_marche_normale_values_between_min_and_max;
    int max_iterations = nb_iterations() / 100;
    int mid_value = 2 ** (VALSIZE - 1);
    input_itf.com = 0;
    $display("Test Marche Normale min <= val < max. Min [0:%d[", max_iterations);
    for (int i = 0; i < max_iterations; ++i) begin
      input_itf.min = i;
      for (int max = input_itf.min + 1; max < max_iterations; ++max) begin
        input_itf.max = max;
        for (int val = input_itf.min; val <= max; ++val) begin
          input_itf.value = val;
          test_both_osci_state();
        end
      end
    end
    $display("Test Marche Normale min <= val < max. Min [%d:%d[", max_value() - max_iterations,
             max_value());
    for (int i = 0; i < max_iterations; ++i) begin
      input_itf.min = max_value() - max_iterations + i;
      for (int max = input_itf.min + 1; max < max_iterations; ++max) begin
        input_itf.max = max;
        for (int val = input_itf.min; val <= max; ++val) begin
          input_itf.value = val;
          test_both_osci_state();
        end
      end
    end

    $display("Test Marche Normale min <= val < max. Min [%d:%d[", mid_value - (max_iterations / 2),
             mid_value + (max_iterations / 2));
    for (int i = 0; i < max_iterations; ++i) begin
      input_itf.min = mid_value - (max_iterations / 2) + i;
      for (int max = input_itf.min + 1; max < max_iterations; ++max) begin
        input_itf.max = max;
        for (int val = input_itf.min; val <= max; ++val) begin
          input_itf.value = val;
          test_both_osci_state();
        end
      end
    end
  endtask

  task automatic test_every_combination;
    assert (VALSIZE <= 10)
    else $fatal("Can't Run Every combination with VALSIZE > 10");

    input_itf.com = 0;
    for (int val = 0; val < 2 ** VALSIZE; ++val) begin
      for (int min = 0; min <= val; ++min) begin
        for (int max = val + 1; max < 2 ** VALSIZE; ++max) begin
          input_itf.min   = min;
          input_itf.max   = max;
          input_itf.value = val;
          test_both_osci_state();
        end
      end
    end
    for (int com = 1; com <= 3; ++com) begin
      input_itf.com = com;
      for (int val = 0; val < 2 ** VALSIZE; ++val) begin
        input_itf.value = val;
        test_both_osci_state();
      end
    end

  endtask

  task automatic test_marche_normale_values_bigger_than_max;
    Input obj;
    obj = new;
    obj.com = 0;
    obj.value_bigger_than_max_c.constraint_mode(1);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Marche Normale val > max");
    for (int i = 0; i < 10; ++i) begin
      random_or_fatal(obj);
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

    $display("Running Test Marche Normale val < min");
    for (int i = 0; i < 10; ++i) begin
      random_or_fatal(obj);
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_random_values;
    Input obj;
    obj = new;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test With Random Values");
    while (obj.cov_group.get_inst_coverage() < 100) begin
      random_or_fatal(obj);
      obj.cov_group.sample();
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_val_lineaire;
    int max = max_value();
    input_itf.com = 1;
    for(int i = 0; i < VALSIZE; ++i) begin
      input_itf.value = 2**i;
      test_both_osci_state();
    end
  endtask

  task automatic test_eteint;
    Input obj;
    obj = new;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Eteint");
    for (int i = 0; i < 10; ++i) begin
      random_or_fatal(obj);
      obj.com = 2;
      map_obj_to_input_itf(obj);
      test_both_osci_state();
    end
  endtask

  task automatic test_allume_fort;
    int max_iterations = nb_iterations();
    Input obj;
    obj = new;
    obj.value_bigger_than_max_c.constraint_mode(0);
    obj.value_smaller_than_min_c.constraint_mode(0);
    obj.value_between_max_and_min_c.constraint_mode(0);

    $display("Running Test Allume Fort");
    for (int i = 0; i < 10; ++i) begin
      random_or_fatal(obj);
      obj.com = 3;
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
    test_random_values;
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
      7: test_random_values;
      8: test_every_combination;
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
      3: leds = 2 ** (2 ** VALSIZE) - 1;
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
        error_signal = 1;
        #pulse;
        error_signal = 0;
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
      $error("ERROR %d errors detected.", nb_errors);
    end else begin
      $display("OK No errors detected.");
    end


    $finish;
  end

endmodule
