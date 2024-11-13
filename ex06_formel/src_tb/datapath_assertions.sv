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

  function automatic get_last_value;
    logic [ 6:0] result;
    logic [63:0] prev_in = $previous(InPort);
    for (int i = 0, index = $previous(Sel) * 8; i < 7; i++, index++) begin
      result[i] = prev_in[index];
    end
    return result;
  endfunction

  property p_check_mov;
    @(posedge clk) (Wen ##1 Op == 4 && (RAA == $previous(
        WA
    ))) |-> (OutPort == get_last_value());
  endproperty
  assert property (p_check_mov);

  property p_check_shr;
    @(posedge clk) (Wen ##1 Op == 1 && (RAA == $previous(
        WA
    ))) |-> (OutPort == get_last_value() >> 1);
  endproperty
  assert property (p_check_shr);


endmodule
