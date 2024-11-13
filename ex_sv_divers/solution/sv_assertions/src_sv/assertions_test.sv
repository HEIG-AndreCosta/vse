module assertions_test;
  
    logic clk = 0;
    logic req;
    logic ack;
    logic a;
    logic b;
    logic c;
    
    
    // Si une requete arrive (req=1),
    // alors un acknowledge (ack=1) doit etre observé au plus tard 4 cycles apres
    assert1 : assert property 
    (
        @(posedge clk)
        req |=> ##[0:3] ack
    );
    
    // Si A a été à 1 pendant 3 cycles,
    // et que B a été à 1 pendant les deux dernier cycles pendant que A était à 1,
    // alors C doit etre à 0 au cycle suivant
    // et passer de 0 à 1 au plus tard 4 cycles apres
    assert2 : assert property
    (
        @(posedge clk)
        (a ##1 (a&&b)[*2]) |=> !c ##[1:4] c
    );
  
  
  
  
  
  
    // génération de l'horloge
    always #5 clk = ~clk;
    
    
    // clocking block
    default clocking cb @(posedge clk);
    endclocking
    
    task test_case1();
        $display("Let's start test 1");
        req <= 0;
        ack <= 0;
        ##1;
        req <= 1;
        ##1;
        req <= 0;
        ##5;
        ack <= 1;
        
        $display("End of test 1");
        
        
    endtask
    
    task test_case2();
        $display("Let's start test 2");
        
        
        $display("End of test 2");
    endtask
    
    // Programme lancé au démarrage de la simulation
    program TestSuite;
        initial begin
            test_case1();
            test_case2();
            $display("done!");
            $stop;
        end
    endprogram
  
endmodule : assertions_test
