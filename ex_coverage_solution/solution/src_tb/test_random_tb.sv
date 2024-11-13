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

    logic[15:0] a;
    logic[15:0] b;
    logic[15:0] c;
    logic[1:0]  m;

    // clock generation
    always #5 clk = ~clk;

    // clocking block
    default clocking cb @(posedge clk);
    endclocking

    class STest;
        rand logic[7:0] sa;
        rand logic[7:0] sb;

        constraint sb_even_if_sa {
            sa % 2 == 0 -> sb % 2 == 0;
        }
    endclass

    class RTest;
        rand logic[15:0] a;
        rand logic[15:0] b;
        rand logic[15:0] c;
        rand logic[1:0]  m;

        rand STest st[];

        rand logic[3:0] ba;
        rand logic[3:0] bb;

        covergroup cov_group;
            option.auto_bin_max = 1000;
            cov_a: coverpoint a;
            cov_b: coverpoint b;
            cov_c: coverpoint c;
            cov_m: coverpoint m {
                option.at_least = 10000;
                bins valid[3]={0,1,2};
                illegal_bins unvalid = {3};
            }
            // cov_cross: cross cov_a, cov_b;
        endgroup

        function new();
            cov_group = new;
        endfunction

        constraint bab_dist {
            bb dist {
                [0:12]  :/ 90,
                [13:15] :/ 10
            };

            ba dist {
                [0:2]  :/ 75,
                [3:15] :/ 25
            };
        }

        constraint bb_range {
            ba < 3 -> bb > 12;
        }

        constraint m_range {
            m inside {[0:2]};
        }

        constraint ab_range {
            (m == 0) -> a < 10;
            (m == 1) -> b inside {[12:16]};
        }

        constraint c_range {
            c > (a + b);
        }

        constraint st_size {
            st.size() < 20;
        }

        constraint order {
            solve m before a, b;
            solve a, b before c;
            solve ba before bb;
        }

        function void post_randomize();
            for (int i=0; i < st.size(); i++) begin
                st[i] = new;
                void'(st[i].randomize());
            end
        endfunction
    endclass


    task test_case0();
        // Create the object
        static RTest rtest = new();

        int ba_count[16];
        int bb_count[16];

        automatic int nb_cases = 0;

        a = 0;
        b = 0;
        c = 0;
        m = 0;

        ##1;

        repeat (100000) begin
            // Randomize the object
            if(!rtest.randomize()) $stop;

            nb_cases = nb_cases + 1;
            rtest.cov_group.sample();
            if ($get_coverage() == 100.0) begin
                $display("Couverture atteinte après %d cas", nb_cases);
                $stop;
            end
            // $display("Coverage tot: %f", $get_coverage());
            $display("Coverage ins: %f", rtest.cov_group.get_inst_coverage());

            assert(rtest.m inside {[0:2]});
            assert((rtest.m == 0) -> rtest.a < 10);
            assert((rtest.m == 1) -> rtest.b inside {[12:16]});
            assert(rtest.c > rtest.a + rtest.b);
            assert(rtest.st.size() < 20);
            for (int i = 0; i < rtest.st.size(); i++) begin
                assert(rtest.st[i].sa % 2 == 0 -> rtest.st[i].sb % 2 == 0);
            end

            ba_count[rtest.ba]++;
            bb_count[rtest.bb]++;

            // Apply its values to the signals (for nice view in the chronogram)
            a = rtest.a;
            b = rtest.b;
            c = rtest.c;
            m = rtest.m;
            ##1;
        end
        $display("value | nb in ba | nb in bb");
        // YTA : On pourrait sortir la proportion des deux boites ba et deux boites bb
        for (int i = 0; i < 16; i++) begin
            $display("%5d | %7d%% | %7d%%", i, ba_count[i] / 10, bb_count[i]/10);
        end
    endtask

    // Program launched at simulation start
    program TestSuite;
        initial begin
            test_case0();
            $stop;
        end

    endprogram

endmodule
