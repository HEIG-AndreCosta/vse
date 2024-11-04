module avalon_assertions #(
    int AVALONMODE = 0,
    int TESTCASE = 0,
    int NBDATABYTES = 2,
    int NBADDRBITS = 8,
    int WRITEDELAY = 2,  // Delay for fixed delay write operation
    int READDELAY = 1,  // Delay for fixed delay read operation
    int FIXEDDELAY = 2
)  // Delay for pipeline operation
(
    input logic clk,
    input logic rst,

    input logic [   NBADDRBITS-1:0] address,
    input logic [    NBDATABYTES:0] byteenable,
    input logic [2^NBDATABYTES-1:0] readdata,
    input logic [2^NBDATABYTES-1:0] writedata,
    input logic                     read,
    input logic                     write,
    input logic                     waitrequest,
    input logic                     readdatavalid,
    input logic [              7:0] burstcount,
    input logic                     beginbursttransfer
);


  // clocking block
  default clocking cb @(posedge clk);
  endclocking

  // read et write ne doivent jamais être actifs en même temps
  assert_waitreq1 :
  assert property (!(read & write));

  //assert_wait_request_on_rd :
  //assert property ($rose(read) |=> waitrequest);

  //assert_wait_request_on_wr :
  //assert property (write |=> waitrequest);

  assert_rd_or_wr_active_while_wait_request :
  assert property (waitrequest |-> read || write);

  property p_data_is_stable_during_read;
    logic [2^NBDATABYTES-1:0] data;
    @(posedge clk) (read && $fell(
        waitrequest
    ),
    data = readdata
    ) |-> (data == readdata throughout read)
  endproperty

  assert_data_is_stable_during_read :
  assert property (p_data_is_stable_during_read);

  property p_data_is_stable_during_write;
    logic [2^NBDATABYTES-1:0] data;
    @(posedge clk) (write && $fell(
        waitrequest
    ),
    data = writedata
    ) |-> (data == writedata throughout write)
  endproperty

  assert_data_is_stable_during_write :
  assert property (p_data_is_stable_during_write);

endmodule
