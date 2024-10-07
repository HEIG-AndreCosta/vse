/******************************************************************************
Project Math_computer

File : test_random_tb.sv
Description : This module is meant to test some random constructs.
              Currently it is far from being efficient nor useful.

Author : Y. Thoma
Team   : REDS institute

Date   : 07.11.2022

| Modifications |--------------------------------------------------------------
Ver    Date         Who    Description
1.0    07.11.2022   YTA    First version

******************************************************************************/

module test_random_tb;

  logic clk = 0;

  logic [15:0] a;
  logic [15:0] b;
  logic [15:0] c;
  logic [1:0] m;

  // clock generation
  always #5 clk = ~clk;

  // clocking block
  default clocking cb @(posedge clk);
  endclocking


  class RTest;
    rand bit [15:0] a;
    rand bit [15:0] b;
    rand bit [15:0] c;
    rand bit [ 1:0] m;
    constraint m_c {m inside {[0 : 2]};}
    constraint a_c {
      (m == 0) -> a < 10;
      (m == 1) -> b inside {[12 : 16]};
    }

    constraint c_c {c > (a + b);}
    constraint order_a_c {solve m before a, b;}
    constraint order_c_c {solve a, b before c;}

  endclass

  class STest;
    rand bit [7:0] sa;
    rand bit [7:0] sb;

    constraint pair_c {sa[0] == 1'b0 -> sb[0] == 1'b0;}
    constraint order_c {solve sa before sb;}

  endclass


  task automatic test_case0();
    RTest obj;
    a   = 0;
    b   = 0;
    c   = 0;
    m   = 0;

    // Create the object
    obj = new();

    ##1;

    repeat (1000) begin
      // Randomize the object
      assert (obj.randomize())
      else $fatal("No solutions for obj.randomize");

      assert (m >= 0 && m <= 2)
      else $fatal("M constraint failed. Expected  0 <= %d <= 2", obj.m);

      if (obj.m == 0) begin
        assert (obj.a < 10)
        else $fatal("A constraint failed. m == 0. Expected a to be < 10. Actual value: %d", obj.a);
      end else if (obj.m == 1) begin
        assert (obj.b >= 12 && obj.b <= 16)
        else
          $fatal(
              "B constraint failed. m == 1. Expected b to be >= 12 && obj.b <= 16."+
              "Actual value: %d",
              obj.b
          );
      end
      assert (obj.c > obj.a + obj.b)
      else $fatal("C constraint failed. Expected %d > %d + %d.", obj.c, obj.a, obj.b);

      // Apply its values to the signals (for nice view in the chronogram)
      a = obj.a;
      b = obj.b;
      c = obj.c;
      m = obj.m;
      ##1;
    end
  endtask

  task automatic test_case1();

    STest obj;
    // Create the object
    obj = new();

    ##1;
    repeat (1000) begin

      assert (obj.randomize())
      else $fatal("No solutions for obj.randomize");

      if (obj.sa[0] == 1'b0) begin
        assert (obj.sb[0] == 1'b0)
        else $fatal("Expected sb to be pair because sa is pair (%d)", obj.sb);
      end


    end
  endtask



  // Program launched at simulation start
  program TestSuite;
    initial begin
      test_case0();
      test_case1();
      $stop;
    end

  endprogram

endmodule
