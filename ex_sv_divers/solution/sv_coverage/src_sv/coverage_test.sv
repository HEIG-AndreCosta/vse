
class coverage_class; 
    rand logic wr;
    rand logic rd;
    rand logic[1:0] typee;
    rand logic[7:0] address;
    
    covergroup cov_group_type;
  
    // L'ensemble des types doivent avoir été observés
    cov_typee: coverpoint typee;

    // en lecture (rd à 1)
    cov_rd: coverpoint rd
    {
        bins one = {1};
    }
    // et en écriture (wr à 1)
    cov_wr: coverpoint wr
    {
        bins one = {1};
    }
    cov_cross_typee_rd: cross cov_typee, cov_rd;
    cov_cross_typee_wr: cross cov_typee, cov_wr;
  
    // Toutes les adresses entre 0 et 3 et entre 252 et 255 dovent avoir été observées
    cov_address: coverpoint address
    {
        bins lower[4] = {[0:3]};
        bins higher[4] = {[252:255]};
        ignore_bins others = {[4:251]};
    }
    endgroup


    function new();
        cov_group_type = new;
    endfunction : new
  
endclass : coverage_class


module coverage_test;
  
    task test_case1();
        automatic coverage_class obj = new();
        automatic int counter = 0;
    
    
        $display("Let's start test 1");
        
        while ($get_coverage() < 100)
        begin
            counter ++;
            void'(obj.randomize());
            obj.cov_group_type.sample();
        end
        $display("End of test 1 after %d iterations",counter);
      
      
    endtask
    
    
    // Programme lancé au démarrage de la simulation
    program TestSuite;
        initial begin
            test_case1();
            $display("done!");
            $stop;
        end
    endprogram
  
endmodule : coverage_test

