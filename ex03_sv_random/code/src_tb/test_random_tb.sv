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

  class STest;
    rand bit [7:0] sa;
    rand bit [7:0] sb;

    constraint pair_c {sa[0] == 1'b0 -> sb[0] == 1'b0;}
    constraint order_c {solve sa before sb;}

  endclass

  class RTest;
    rand bit [15:0] a;
    rand bit [15:0] b;
    rand bit [15:0] c;
    rand bit [1:0] m;
    rand STest s;
    rand STest s_tab[];
    constraint m_c {m inside {[0 : 2]};}
    constraint a_c {
      (m == 0) -> a < 10;
      (m == 1) -> b inside {[12 : 16]};
    }

    constraint m_dist_c {
      m dist {
        0 := 9,
        1 := 1
      };
    }
    constraint c_c {c > (a + b);}
    constraint order_a_c {solve m before a, b;}
    constraint order_c_c {solve a, b before c;}
    function new();
      s = new;
    endfunction
    function void post_randomize();
      //if (super) super.post_randomize;
      for (int i = 0; i < s_tab.size; ++i) begin
        s_tab[i] = new;
        assert (s_tab[i].randomize())
        else $fatal("No solutions for s_tab[i].randomize");
      end
    endfunction

  endclass



  function automatic void verify(RTest obj);

    assert (obj.m >= 0 && obj.m <= 2)
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

    if (obj.s.sa[0] == 1'b0) begin
      assert (obj.s.sb[0] == 1'b0)
      else $fatal("Expected sb to be pair because sa is pair (%d)", obj.s);
    end
  endfunction

  task automatic test_case0();
    int   count;
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

      verify(obj);
      if (obj.a >= 10) begin
        ++count;
      end

      // Apply its values to the signals (for nice view in the chronogram)
      a = obj.a;
      b = obj.b;
      c = obj.c;
      m = obj.m;
      ##1;
    end
    $display("A was > 10 %d times with constraint on", count);
    count = 0;
    obj.m_dist_c.constraint_mode(0);

    repeat (1000) begin
      // Randomize the object

      assert (obj.randomize())
      else $fatal("No solutions for obj.randomize");


      verify(obj);

      if (obj.a >= 10) begin
        ++count;
      end
      // Apply its values to the signals (for nice view in the chronogram)
      a = obj.a;
      b = obj.b;
      c = obj.c;
      m = obj.m;
      ##1;
    end
    $display("A was > 10 %d times with constraint off", count);
  endtask




  // Program launched at simulation start
  program TestSuite;
    initial begin
      test_case0();
      $stop;
    end

  endprogram

endmodule
