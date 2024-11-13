class constraints_class; 
    rand logic wr;
    rand logic rd;
    rand logic cs;
    rand logic[1:0] typee;
    rand logic[7:0] address;
    rand logic[31:0] data;
    rand logic parity;
    
    constraint value {
        // si cs vaut 0, alors address doit aussi valoir 0
        !cs -> address == 0;
        // si wr vaut 1, alors rd doit valoir 0
        wr -> rd == 0;
        // si rd vaut 1, alors wr doit valoir 0
        rd -> wr == 0;
    }
    
    constraint order {
        solve cs before address;
        solve wr before rd;
        solve typee before address;
    }

    constraint typ {
        typee inside {[0:2]};
    }

    constraint addr {
        typee == 0 -> address < 16;
        typee == 1 -> address inside {[16:127]};
        typee == 2 -> address >= 128; 
    }

    
    // YTA: Bien que ça fonctionne dans ce cas, on avait des contraintes
    // du type "si type vaut alors address vaut". Il me semble plus pertinent
    // de garder cette sémantique dans l'écriture de la contrainte.
    // Celle-ci pourrait plutôt être une contrainte plutôt que d'être post-randomisée
    function void post_randomize();
        // si type vaut 0, alors address < 16
        if (address < 16)
            typee = 0;
        // sit type vaut 1, alors 16<=address<128
        else if (address < 128)
            typee = 1;
        // si type vaut 2, alors 128<=address
        else
            typee = 2;
        // faire comme ça évite de d'avoir le cas type = 3 (indéfini)
        
        // parity doit valoir 0 si la somme des bits à 1 de data est paire, et doit valoir sinon
        // (somme des bits => addition du poids de chaque bit : 1110 => 14 donc pair)
        parity = ~data;
        
    endfunction
  
endclass : constraints_class


module constraints_test;
  
    task test_case1();
        automatic constraints_class obj = new();
    
    
        $display("Let's start test 1");
        
        for(int i=0;i<100;i++)
        begin
            void'(obj.randomize());
            $display("cs = %d, wr = %d, rd = %d, typee = %d, address = %d, data = %d, parity = %d",
                obj.cs, obj.wr, obj.rd, obj.typee, obj.address, obj.data, obj.parity);
        end    
        $display("End of test 1");
      
      
    endtask
    
    
    // Programme lancé au démarrage de la simulation
    program TestSuite;
        initial begin
            test_case1();
            $display("done!");
            $stop;
        end
    endprogram
  
endmodule : constraints_test
