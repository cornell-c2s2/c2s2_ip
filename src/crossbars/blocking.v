`ifndef PROJECT_CROSSBAR_V
`define PROJECT_CROSSBAR_V 

//Crossbar in Verilog

module crossbars_Blocking #(
  parameter int BIT_WIDTH = 32,
  parameter int N_INPUTS = 2,
  parameter int N_OUTPUTS = 2,
  localparam int CONTROL_BIT_WIDTH = $clog2(N_INPUTS * N_OUTPUTS)
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_INPUTS],
  input  logic                   recv_val[N_INPUTS],
  output logic                   recv_rdy[N_INPUTS],

  output logic [BIT_WIDTH - 1:0] send_msg[N_OUTPUTS],
  output logic                   send_val[N_OUTPUTS],
  input  logic                   send_rdy[N_OUTPUTS],

  input logic reset,
  input logic clk,

  input  logic [CONTROL_BIT_WIDTH - 1:0] control,
  input  logic                           control_val,
  output logic                           control_rdy
);

  logic [CONTROL_BIT_WIDTH - 1:0] stored_control;
  logic [$clog2(N_INPUTS)  - 1:0] input_sel;
  logic [$clog2(N_OUTPUTS) - 1:0] output_sel;

  always @(posedge clk) begin
    if (reset) begin
      stored_control <= 0;
    end else if (control_val) begin
      stored_control <= control;
    end
  end

  assign control_rdy = 1;



  assign input_sel = stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)];

  assign output_sel = stored_control[CONTROL_BIT_WIDTH-$clog2(
      N_INPUTS
  )-1 : CONTROL_BIT_WIDTH-$clog2(
      N_INPUTS
  )-$clog2(
      N_OUTPUTS
  )];

  always_comb begin
    send_msg[output_sel] = recv_msg[input_sel];
    send_val[output_sel] = recv_val[input_sel];
    recv_rdy[input_sel]  = send_rdy[output_sel];

    for (integer i = 0; i < N_OUTPUTS; i = i + 1) begin
      if ((i != output_sel)) begin
        send_msg[i] = 0;
        send_val[i] = 0;
      end
    end
    for (integer i = 0; i < N_INPUTS; i = i + 1) begin
      if ((i != input_sel)) begin
        recv_rdy[i] = 0;
      end
    end
  end

endmodule

`endif
