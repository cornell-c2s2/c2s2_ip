//================================================
// template.v
//================================================
`ifndef TEMPLATE_V
`define TEMPLATE_V

module template #(
  parameter width = 32
) (
  input clk,
  input logic reset,

  output logic recv_rdy,
  input logic recv_val,
  input logic [Width-1:0] recv_msg,

  input logic send_rdy,
  output logic send_val,
  output logic [Width-1:0] send_msg
);
  always @(*) begin
    send_msg = recv_msg;
  end
endmodule

`endif
