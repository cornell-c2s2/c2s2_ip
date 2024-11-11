//================================================
// lbist_controller.v
//================================================
`default_nettype none
`ifndef LBIST_CONTROLLER_V
`define LBIST_CONTROLLER_V

module lbist_controller_LbistController #(
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
