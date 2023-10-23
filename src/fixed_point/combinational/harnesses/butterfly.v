`default_nettype none
`include "src/fixed_point/combinational/butterfly.v"
`include "src/serdes/serializer.v"
`include "src/serdes/deserializer.v"

module HarnessFXPMB #(
  parameter int n = 32,
  parameter int d = 16,
  parameter byte mult = 1,
  parameter int b = 4
) (
  input logic clk,
  input logic reset,

  input logic recv_val,
  output logic recv_rdy,
  input logic [6*n-1:0] recv_msg,

  output logic send_val,
  input logic send_rdy,
  output logic [4*n-1:0] send_msg
);

  logic b_recv_rdy;
  logic b_recv_val;
  logic b_send_rdy;
  logic b_send_val;

  logic [6*n-1:0] recv_msg_unpacked[b];
  logic [4*n-1:0] send_msg_unpacked[b];
  logic [n-1:0] ar[b];
  logic [n-1:0] ac[b];
  logic [n-1:0] br[b];
  logic [n-1:0] bc[b];
  logic [n-1:0] wr[b];
  logic [n-1:0] wc[b];

  logic [n-1:0] cr[b];
  logic [n-1:0] cc[b];
  logic [n-1:0] dr[b];
  logic [n-1:0] dc[b];

  Deserializer #(
    .N_SAMPLES(b),
    .BIT_WIDTH(6*n)
  ) deser (
    .recv_rdy(recv_rdy),
    .recv_val(recv_val),
    .recv_msg(recv_msg),
    .send_rdy(b_recv_rdy),
    .send_val(b_recv_val),
    .send_msg(recv_msg_unpacked),
    .*
  );

  Serializer #(
    .N_SAMPLES(b),
    .BIT_WIDTH(4*n)
  ) ser (
    .recv_rdy(b_send_rdy),
    .recv_val(b_send_val),
    .recv_msg(send_msg_unpacked),
    .send_rdy(send_rdy),
    .send_val(send_val),
    .send_msg(send_msg),
    .*
  );

  genvar i;
  generate for(i = 0; i < b; i++) begin : g_loop
    assign ar[i] = recv_msg_unpacked[i][6*n-1:5*n];
    assign ac[i] = recv_msg_unpacked[i][5*n-1:4*n];
    assign br[i] = recv_msg_unpacked[i][4*n-1:3*n];
    assign bc[i] = recv_msg_unpacked[i][3*n-1:2*n];
    assign wr[i] = recv_msg_unpacked[i][2*n-1:n];
    assign wc[i] = recv_msg_unpacked[i][n-1:0];

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

    .recv_val(b_recv_val),
    .recv_rdy(b_recv_rdy),
    .ar(ar),
    .ac(ac),
    .br(br),
    .bc(bc),
    .wr(wr),
    .wc(wc),

    .send_val(b_send_val),
    .send_rdy(b_send_rdy),
    .cr(cr),
    .cc(cc),
    .dr(dr),
    .dc(dc)
  );

endmodule
