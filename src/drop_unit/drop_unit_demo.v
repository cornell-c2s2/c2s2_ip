//================================================
// drop_unit.v
//================================================
`default_nettype none
`ifndef DROP_UNIT_DEMO_V
`define DROP_UNIT_DEMO_V 

`include "drop_unit/drop_unit.v"
`include "fft/pease/fft.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"

module drop_unit_demo #(
  parameter int N_BITS = 16,
  parameter int DECIMAL_BITS = 8,
  parameter int MAX_N_CYCLES = 20,
  parameter int FFT_ARRAY_LENGTH = 32
) (
  input  logic  clk,
  input  logic  reset,

  input  logic  enable,
  input  logic  enable_val,
 
  input  logic [N_BITS-1:0]                req_msg,
  input  logic                             req_val,
  output logic                             req_rdy,
 
  output logic [N_BITS-1:0]                resp_msg,
  output logic                             resp_val,
  input  logic                             resp_rdy,
 
  input  logic [$clog2(MAX_N_CYCLES)-1:0]  cfg_drop_msg,
  input  logic                             cfg_drop_val,
  output logic                             cfg_drop_rdy
);
  logic                                    drop_deser_resp_val;
  logic [N_BITS-1:0]                       drop_deser_resp_msg;
  logic                                    drop_deser_resp_rdy;

  logic                                    deser_fft_resp_val;
  logic [N_BITS-1:0]                       deser_fft_resp_msg [FFT_ARRAY_LENGTH];
  logic                                    deser_fft_resp_rdy;

  logic                                    fft_ser_resp_val;
  logic [N_BITS-1:0]                       fft_ser_resp_msg   [FFT_ARRAY_LENGTH];
  logic                                    fft_ser_resp_rdy;

  drop_unit #(
    .N_BITS(N_BITS),
    .MAX_N_CYCLES(MAX_N_CYCLES)
  ) drop_unit (
    .clk         (clk),
    .reset       (reset),
    .enable      (enable),
    .enable_val  (enable_val),
    .req_msg     (req_msg),
    .req_val     (req_val),
    .req_rdy     (req_rdy),
    .resp_msg    (drop_deser_resp_msg),
    .resp_val    (drop_deser_resp_val),
    .resp_rdy    (drop_deser_resp_rdy),
    .cfg_drop_msg(cfg_drop_msg),
    .cfg_drop_val(cfg_drop_val),
    .cfg_drop_rdy(cfg_drop_rdy)
  );
  
  serdes_Deserializer #(
    .N_SAMPLES(FFT_ARRAY_LENGTH),
    .BIT_WIDTH(N_BITS)
  ) serdes_Deserializer (
    .clk     (clk),
    .reset   (reset),
    .recv_val(drop_deser_resp_val),
    .recv_rdy(drop_deser_resp_rdy),
    .recv_msg(drop_deser_resp_msg),
    .send_val(deser_fft_resp_val),
    .send_rdy(deser_fft_resp_rdy),
    .send_msg(deser_fft_resp_msg)
  );
  
  fft_pease_FFT #(
    .BIT_WIDTH(N_BITS),
    .DECIMAL_PT(DECIMAL_BITS),
    .N_SAMPLES(FFT_ARRAY_LENGTH)
  ) fft_pease_FFT (
    .clk     (clk),
    .reset   (reset),
    .recv_msg(deser_fft_resp_msg),
    .recv_val(deser_fft_resp_val),
    .recv_rdy(deser_fft_resp_rdy),
    .send_msg(fft_ser_resp_msg),
    .send_val(fft_ser_resp_val),
    .send_rdy(fft_ser_resp_rdy)
  );
  
  serdes_Serializer #(
    .N_SAMPLES(FFT_ARRAY_LENGTH/2),
    .BIT_WIDTH(N_BITS)
  ) serdes_Serializer (
    .clk     (clk),
    .reset   (reset),
    .recv_val(fft_ser_resp_val),
    .recv_rdy(fft_ser_resp_rdy),
    .recv_msg(fft_ser_resp_msg[0:FFT_ARRAY_LENGTH/2-1]),
    .send_val(resp_val),
    .send_rdy(resp_rdy),
    .send_msg(resp_msg)
  );

endmodule

`endif