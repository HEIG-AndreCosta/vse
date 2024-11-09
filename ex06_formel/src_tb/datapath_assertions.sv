module datapath_assertions (
    input logic        clk,
    input logic [63:0] InPort,
    input logic [ 6:0] OutPort,
    input logic [ 7:0] Ctrl,
    input logic [ 3:0] Sel,
    input logic        Wen,
    input logic [ 3:0] WA,
    input logic [ 3:0] RAA,
    input logic [ 3:0] RAB,
    input logic [ 2:0] Op,
    input logic        Flag
);
  //`define ASSERT_PROP(p) assert property (@(posedge clk) p);

  function automatic get_value;
    logic [7:0] result;
    for (int i = 0, index = Sel * 8; i < 8; i++, index++) begin
      result[i] = InPort[index];
    end
    return result;
  endfunction

  property p_basic_check;
    logic [7:0] value
    ;
    logic [3:0] address;
    @(posedge clk) (Wen,
    address = WA
    ,
    value = get_value()
    ) |=> ((##[0:$] (Op == 4 && RAA == address))) |-> (OutPort == value[6:0]);
  endproperty
  assert property (p_basic_check);
endmodule
