// ===================================================================
// Author: Johnny Martinez
// Date: 04/14/2025
// Documentation: 
// Spec: Blocking crossbar where each input/output port is composed 
// of a 2-d array.
// PARAMETERS --------------------------------------------------------
// BIT_WIDTH: Width of the data bus.
// N_INPUTS: Number of inputs to the crossbar.
// N_OUTPUTS: Number of outputs to the crossbar.
// ENTRIES: Number of entries per input/output port.
// CONTROL_BIT_WIDTH: Number of bits needed to select the input/output
// port.
// I/O ---------------------------------------------------------------
// - clk
// - reset
// - recv_msg: Input data to the crossbar.
// - recv_val: Valid signals for the input data.
// - recv_rdy: Ready signals for the input data.
// - send_msg: Output data from the crossbar.
// - send_val: Valid signals for the output data.
// - send_rdy: Ready signals for the output data.
// - control: Control signals to select the input/output port.
// - control_val: Valid signal for the control signals.
// - control_rdy: Ready signal for the control signals.

// https://www.chipverify.com/verilog/verilog-arrays-memories
// reg  [7:0] y3 [0:1][0:3];    // y is a 2D array rows=2,cols=4 each 8-bit wide
// ===================================================================

`ifndef CROSSBAR_2D_V
`define CROSSBAR_2D_V
`define VL_RD

module crossbar_2d#(
    parameter int BIT_WIDTH = 32,
    parameter int N_INPUTS = 2,
    parameter int N_OUTPUTS = 2,
    parameter int ENTRIES = 2,
    localparam int CONTROL_BIT_WIDTH = $clog2(N_INPUTS * N_OUTPUTS)
  ) (
    input logic                   clk,
    input logic                   reset,

    input  logic [BIT_WIDTH - 1:0] recv_msg [N_INPUTS][ENTRIES],
    input  logic                   recv_val [N_INPUTS],
    output logic                   recv_rdy [N_INPUTS],
  
    output logic [BIT_WIDTH - 1:0] send_msg [N_OUTPUTS][ENTRIES],
    output logic                   send_val [N_OUTPUTS],
    input  logic                   send_rdy [N_OUTPUTS],

    input  logic [CONTROL_BIT_WIDTH - 1:0] control,
    input  logic                           control_val,
    output logic                           control_rdy
  );

//============================LOCAL_PARAMETERS=================================
  logic [CONTROL_BIT_WIDTH - 1:0] stored_control;
  logic [$clog2(N_INPUTS)  - 1:0] input_sel;
  logic [$clog2(N_OUTPUTS) - 1:0] output_sel;

//================================DATAPATH=====================================
  // Control logic
  always_ff @(posedge clk) begin
    if (reset) begin
      stored_control <= 0;
    end else if (control_val) begin
      stored_control <= control;
    end else begin
      stored_control <= stored_control;
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
    for (int i = 0; i < N_OUTPUTS; i = i + 1) begin
      if ((i != output_sel)) begin
        for (int j = 0; j < ENTRIES; j = j + 1) begin
          send_msg[i][j] = 0;
        end
        send_val[i] = 0;
      end else begin
        for (int j = 0; j < ENTRIES; j = j + 1) begin
          send_msg[output_sel][j] = recv_msg[input_sel][j];
        end
        send_val[i] = recv_val[input_sel];
      end
    end
  
    for (int i = 0; i < N_INPUTS; i = i + 1) begin
      if ((i != input_sel)) begin
        recv_rdy[i] = 0;
      end else begin
        recv_rdy[i] = send_rdy[output_sel];
      end
    end

  end

endmodule
`endif
