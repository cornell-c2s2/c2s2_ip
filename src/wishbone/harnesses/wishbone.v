`default_nettype none
`include "wishbone/wishbone.v"

module wishbone_harnesses_WishboneHarness #(
  parameter int n_modules = 1
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [71+32*n_modules+2*n_modules-1:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [32*(n_modules-1)+31 + 33+2*n_modules:0] send_msg
);

// proc -> wb
// recv_msg
//     69          68        67       66:64      63:32     31:0
// +----------+---------+---------+---------+----------+-----------+
// wbs_stb_i  wbs_cyc_i  wbs_we_i  wbs_sel_i  wbs_dat_i  wbs_adr_i

// wb -> proc
// resp_msg
//    32         31:0
// +----------+---------+
//  wbs_ack_o  wbs_dat_o

assign recv_rdy = 1;
assign send_val = 1;

logic [31:0] con_o_stream_data [n_modules];
logic [31:0] con_i_stream_data [n_modules];

genvar i;
generate
  for (i = 0; i < n_modules; i = i + 1) begin
    assign con_o_stream_data[i] = recv_msg[32*i+31 + 71:32*i+71];
  end
endgenerate

genvar j;
generate
  for (j = 0; j < n_modules; j = j + 1) begin
    assign send_msg[32*j+31 + 33+2*n_modules :33+2*n_modules + 32*j] = con_i_stream_data[j];
  end
endgenerate

// generate
//     for (i = 0; i < noutputs; i = i + 1) begin : output_gen
//       assign out[i] = (i == sel) ? in : {nbits{1'b0}};
//     end
//   endgenerate


Wishbone #(n_modules) wb (
  //inputs
  .clk(clk),
  .reset(reset),
  .i_stream_rdy(recv_msg[71+32*n_modules+2*n_modules-1:71+32*n_modules+n_modules]),
  .o_stream_val(recv_msg[71+32*n_modules+n_modules-1:71+32*n_modules]),
  .o_stream_data(con_o_stream_data),
  .wbs_stb_i(recv_msg[70]),
  .wbs_cyc_i(recv_msg[69]),
  .wbs_we_i(recv_msg[68]),
  .wbs_sel_i(recv_msg[67:64]),
  .wbs_dat_i(recv_msg[63:32]),
  .wbs_adr_i(recv_msg[31:0]),
  //outputs
  .i_stream_data(con_i_stream_data),
  .o_stream_rdy(send_msg[33+2*n_modules-1:33+n_modules]),
  .i_stream_val(send_msg[33+n_modules-1:33]),
  .wbs_ack_o(send_msg[32]),
  .wbs_dat_o(send_msg[31:0])
);

endmodule
