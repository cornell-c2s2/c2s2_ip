//================================================
// template.v
//================================================
`ifndef TEMPLATE_V
`define TEMPLATE_V

<<<<<<< HEAD:template/template.v
module Template #(
  parameter int width = 32
) (
  input  logic clk,
  input  logic reset,

  output logic recv_rdy,
  input  logic recv_val,
  input  logic [width - 1:0] recv_msg,
=======
module template #(
  parameter width = 32
) (
  input clk,
  input logic reset,

  output logic recv_rdy,
  input logic recv_val,
  input logic [Width-1:0] recv_msg,
>>>>>>> 1ec3219... updates imports:template/Template.v

  input  logic send_rdy,
  output logic send_val,
<<<<<<< HEAD:template/template.v
  output logic [width - 1:0] send_msg
=======
  output logic [Width-1:0] send_msg
>>>>>>> 1ec3219... updates imports:template/Template.v
);
  always @(*) begin
    send_msg = recv_msg;
  end
endmodule

`endif