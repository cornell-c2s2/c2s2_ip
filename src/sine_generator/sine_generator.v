//================================================
// sine_generator.v
//================================================
`default_nettype none
`ifndef SINE_GENERATOR_V
`define SINE_GENERATOR_V

module SineGenerator #(
  parameter int Width = 32
) (
  input logic clk,
  input logic reset,

  output logic recv_rdy,
  input logic recv_val,
  input logic [Width - 1:0] recv_msg,

  input logic send_rdy,
  output logic send_val,
  output logic [Width - 1:0] send_msg
);
  always_comb begin
    send_msg = recv_msg;
  end
endmodule

`endif
