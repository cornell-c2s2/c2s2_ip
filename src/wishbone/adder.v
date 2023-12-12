//================================================
// wishbone.v
//================================================
`default_nettype none
`ifndef ADDER_V
`define ADDER_V

module Adder (

  input clk,
  input reset,

  // Ports to connect to modules
  output logic i_stream_rdy,
  input logic i_stream_val,
  input logic o_stream_rdy,
  output logic o_stream_val,
  output logic [31:0] o_stream_data,
  input logic [31:0] i_stream_data

);

  logic [31:0] reg_out;
  logic reg_en;
  assign reg_en = i_stream_val;
  always_ff @(posedge clk) begin
    if (reset) reg_out <= 32'b0;
    else if (reg_en) reg_out <= i_stream_data;
  end
  assign o_stream_data = reg_out + 1;

  localparam INPUT_READY = 1'b0;
  localparam OUTPUT_READY = 1'b1;

  logic state, next_state;

  always_ff @(posedge clk) begin
    if (reset) state <= INPUT_READY;
    else state <= next_state;
  end

  always_comb begin
    next_state = state;
    case (state)
      INPUT_READY: begin
        if (i_stream_val) next_state = OUTPUT_READY;
      end
      OUTPUT_READY: begin
        if (o_stream_rdy) next_state = INPUT_READY;
      end
    endcase
  end

  always_comb begin
    case (state)
      INPUT_READY: begin
        i_stream_rdy = 1'b1;
        o_stream_val = 1'b0;
      end
      OUTPUT_READY: begin
        i_stream_rdy = 1'b0;
        o_stream_val = 1'b1;
      end
      default: begin
        i_stream_rdy = 1'bx;
        o_stream_val = 1'bx;
      end
    endcase
  end

endmodule

`endif
