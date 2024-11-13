module avalon_assertions #(
                           int AVALONMODE = 0,
                           int TESTCASE = 0,
                           int NBDATABYTES = 2,
                           int NBADDRBITS = 8,
                           int WRITEDELAY = 2,  // Delay for fixed delay write operation
                           int READDELAY = 1,   // Delay for fixed delay read operation
                           int FIXEDDELAY = 2)  // Delay for pipeline operation
   (
    input logic                     clk,
    input logic                     rst,

    input logic [NBADDRBITS-1:0]    address,
    input logic [NBDATABYTES:0]     byteenable,
    input logic [2^NBDATABYTES-1:0] readdata,
    input logic [2^NBDATABYTES-1:0] writedata,
    input logic                     read,
    input logic                     write,
    input logic                     waitrequest,
    input logic                     readdatavalid,
    input logic [7:0]               burstcount,
    input logic                     beginbursttransfer
    );


    // clocking block
    default clocking cb @(posedge clk);
    endclocking

    // read et write ne doivent jamais être actifs en même temps
    assert_waitreq1:
    assert property (!(read & write));

    // waitrequest actif implique read ou write
    // ( = waitrequest n'est actif que lorsque read ou write est actif)
    assert_waitreq3:
        assert property (waitrequest |-> (read or write));

    // Si read et waitrequest sont actifs, alors read doit rester actif
    assert_waitreq4:
        assert property ((read & waitrequest) |=> (read));

    assert_waitreq5:
        assert property ($rose(write) |=> (write -> ($stable(address) & $stable(byteenable) & $stable(writedata))));

    // Si read est actif pendant au moins 2 cycles d'horloge, alors l'adresse et byteenable
    // doivent être stables
    assert_waitreq6:
        assert property ((read[*2]) |-> ($stable(address) & $stable(byteenable)));

    // Si write est actif pendant au moins 2 cycles d'horloge, alors l'adresse, writedata et byteenable
    // doivent être stables
    assert_waitreq7:
        assert property (write[*2] |-> ($stable(address) & $stable(byteenable) & $stable(writedata)));

    // Si read et waitrequest sont actifs, alors l'adresse doit être stable au cycle suivant
    assert_waitreq8:
        assert property ((read & waitrequest) |=> ($stable(address)));

    // Si read est actif, alors si waitrequest est actif alors l'adresse doit être stable au
    // cycle suivant
    assert_waitreq9:
        assert property (read |-> (waitrequest |=> ($stable(address))));

    // Lorsque read devient actif, alors jusqu'à ce qu'il redevienne inactif on peut observer
    // un nombre quelconque de waitrequest suivi de waitrequest à 0
    assert_waitreq10:
        assert property ($rose(read) |-> ((read[*1:$] ##1 !read) intersect (waitrequest[*0:$] ##1 ((!waitrequest)) ##1 1)));

    // Lorsque write devient actif, alors jusqu'à ce qu'il redevienne inactif on peut observer
    // un nombre quelconque de waitrequest suivi de waitrequest à 0
    assert_waitreq11:
        assert property ($rose(write) |-> ((write[*1:$] ##1 !write) intersect (waitrequest[*0:$] ##1 ((!waitrequest)) ##1 1)));
             
    // A la fin d'une écriture, lorsque waitrequest vaut 0, alors le signal write doit redescendre
    assert_waitreq12:
        assert property ((write & !waitrequest) |=> ($fell(write)));  

    // A la fin d'une lecture, lorsque waitrequest vaut 0, alors le signal read doit redescendre
    assert_waitreq13:
        assert property ((read & !waitrequest) |=> ($fell(read)));  


    // Pendant une lecture avec waitrequest=1, l'addresse doit rester stable
    // Qu'est-ce qui n'est pas idéal ici?
    assert_waitreq_humair2:
    assert property (@(posedge clk) disable iff (rst)
        (read && waitrequest) |=> $stable(address) until_with !waitrequest);

    // Version améliorée
    assert_waitreq_humair2b:
    assert property (@(posedge clk) disable iff (rst)
        ($rose(read) && waitrequest) |=> $stable(address) until_with !waitrequest);

endmodule
