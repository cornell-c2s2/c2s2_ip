`default_nettype none
`include "src/fixed_point/combinational/butterfly.v"
`include "src/serdes/serializer.v"
`include "src/serdes/deserializer.v"

module HarnessFXPMB #(
  parameter int n = 32,
  parameter int d = 16,
  parameter int b = 4
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [6*n*b-1:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [4*n*b-1:0] send_msg
);

  logic [6*n-1:0] recv_msg_unpacked[b-1:0];
  logic [4*n-1:0] send_msg_unpacked[b-1:0];
  logic [n-1:0] ar[b-1:0];
  logic [n-1:0] ac[b-1:0];
  logic [n-1:0] br[b-1:0];
  logic [n-1:0] bc[b-1:0];
  logic [n-1:0] wr[b-1:0];
  logic [n-1:0] wc[b-1:0];
  logic [n-1:0] cr[b-1:0];
  logic [n-1:0] cc[b-1:0];
  logic [n-1:0] dr[b-1:0];
  logic [n-1:0] dc[b-1:0];

  generate for (genvar i = 0; i < b; i++) begin : g_loop
    assign recv_msg_unpacked[i] = recv_msg[6*n*(i+1)-1:6*n*i];
    assign ar[i] = recv_msg_unpacked[i][6*n-1:5*n];
    assign ac[i] = recv_msg_unpacked[i][5*n-1:4*n];
    assign br[i] = recv_msg_unpacked[i][4*n-1:3*n];
    assign bc[i] = recv_msg_unpacked[i][3*n-1:2*n];
    assign wr[i] = recv_msg_unpacked[i][2*n-1:n];
    assign wc[i] = recv_msg_unpacked[i][n-1:0];

    assign send_msg[4*n*(i+1)-1:4*n*i] = send_msg_unpacked[i];
    assign send_msg_unpacked[i][4*n-1:3*n] = cr[i];
    assign send_msg_unpacked[i][3*n-1:2*n] = cc[i];
    assign send_msg_unpacked[i][2*n-1:n] = dr[i];
    assign send_msg_unpacked[i][n-1:0] = dc[i];
    end
  endgenerate

  // always_comb begin
  //   $display("recv %d %x",0,recv_msg_unpacked[0]);
  //   $display("send %d %x",0,send_msg_unpacked[0]);
  //   $display("recv %d %x",1,recv_msg_unpacked[1]);
  //   $display("send %d %x",1,send_msg_unpacked[1]);
  // end

  FixedPointMultiButterfly #(
    .n(n),
    .d(d),
    .b(b)
  ) btfly (
    .clk  (clk),
    .reset(reset),

    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .ar(ar),
    .ac(ac),
    .br(br),
    .bc(bc),
    .wr(wr),
    .wc(wc),

    .send_val(send_val),
    .send_rdy(send_rdy),
    .cr(cr),
    .cc(cc),
    .dr(dr),
    .dc(dc)
  );

endmodule
