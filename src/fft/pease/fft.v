
`ifndef FIXED_POINT_FFT
`define FIXED_POINT_FFT

`include "src/fft/helpers/sine_wave.v"
`include "src/fft/helpers/bit_reverse.v"
`include "src/fixed_point/combinational/butterfly.v"
`include "src/fft/pease/helpers/stride_permutation.v"
`include "src/fft/cooley_tukey/helpers/twiddle_generator.v"

module FFT #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES - 1:0],
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES - 1:0],
  output logic                   send_val,
  input  logic                   send_rdy,

  input logic reset,
  input logic clk
);

  logic [2:0] IDLE = 3'd0, COMP = 3'd1, DONE = 3'd2;

  localparam int BstageBits = (N_SAMPLES > 2) ? $clog2($clog2(N_SAMPLES)) + 1 : 1;
  logic [BstageBits-1:0] max_bstage = $clog2(N_SAMPLES);

  logic [2:0] state;
  logic [2:0] next_state;

  assign recv_rdy = (state == IDLE);
  assign send_val = (state == DONE);

  logic [BstageBits-1:0] bstage;
  logic [BstageBits-1:0] next_bstage;

  logic [2 * BIT_WIDTH - 1:0] in_stride         [N_SAMPLES - 1:0];
  logic [2 * BIT_WIDTH - 1:0] in_butterfly      [N_SAMPLES - 1:0];
  logic [2 * BIT_WIDTH - 1:0] out_butterfly     [N_SAMPLES - 1:0];

  logic [BIT_WIDTH - 1:0] reversed_msg [N_SAMPLES - 1:0];
  BitReverse #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) bit_reverse (
    .in (recv_msg),
    .out(reversed_msg)
  );

  StridePermutation #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH*2)
  ) stride_permutation (
    .recv (in_stride),
    .send (in_butterfly)
  );

  logic [BIT_WIDTH - 1:0] sine_wave_out     [0:N_SAMPLES - 1];
  logic [BIT_WIDTH - 1:0] wr                [$clog2(N_SAMPLES)-1:0][N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] wc                [$clog2(N_SAMPLES)-1:0][N_SAMPLES/2 - 1:0];

  generate
    for (genvar i = 0; i < $clog2(N_SAMPLES); i++) begin
      TwiddleGenerator #(
        .BIT_WIDTH (BIT_WIDTH),
        .DECIMAL_PT(DECIMAL_PT),
        .SIZE_FFT  (N_SAMPLES),
        .STAGE_FFT (i)
      ) twiddle_generator (
        .sine_wave_in(sine_wave_out),
        .twiddle_real(wr[i]),
        .twiddle_imaginary(wc[i])
      );
    end
  endgenerate

  SineWave #(
    .N(N_SAMPLES),
    .W(BIT_WIDTH),
    .D(DECIMAL_PT)
  ) sine_wave (
    .sine_wave_out(sine_wave_out)
  );


  logic [BIT_WIDTH - 1:0] ar [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] ac [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] br [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] bc [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] cr [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] cc [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] dr [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] dc [N_SAMPLES/2 - 1:0];
  logic butterfly_send_rdy = 1'b1;
  logic butterfly_send_val;
  logic butterfly_recv_val = (state == COMP);
  logic butterfly_recv_rdy;

  generate
    for (genvar i = 0; i < N_SAMPLES/2; i++) begin
      assign ar[i] = in_butterfly[i*2][BIT_WIDTH - 1:0];
      assign ac[i] = in_butterfly[i*2][2*BIT_WIDTH - 1:BIT_WIDTH];
      assign br[i] = in_butterfly[i*2 + 1][BIT_WIDTH - 1:0];
      assign bc[i] = in_butterfly[i*2 + 1][2*BIT_WIDTH - 1:BIT_WIDTH];
      assign out_butterfly[i*2][BIT_WIDTH - 1:0]               = cr[i];
      assign out_butterfly[i*2][2*BIT_WIDTH - 1:BIT_WIDTH]     = cc[i];
      assign out_butterfly[i*2 + 1][BIT_WIDTH - 1:0]           = dr[i];
      assign out_butterfly[i*2 + 1][2*BIT_WIDTH - 1:BIT_WIDTH] = dc[i];
    end
  endgenerate

  FixedPointMultiButterfly #(
    .n(BIT_WIDTH),
    .d(DECIMAL_PT),
    .b(N_SAMPLES/2)
  ) fft_stage (
    .recv_val(butterfly_recv_val),
    .recv_rdy(butterfly_recv_rdy),
    .send_val(butterfly_send_val),
    .send_rdy(butterfly_send_rdy),
    .wr(wr[bstage]),
    .wc(wc[bstage]),
    .*
  );

  always_comb begin
    next_state = state;
    next_bstage = bstage;
    if (state == IDLE && recv_val) begin
      next_state = COMP;
    end else if (state == COMP && butterfly_send_val) begin
      if (bstage == max_bstage - 1) begin
        next_state = DONE;
        next_bstage = 0;
      end else begin
        next_bstage = bstage + 1;
      end
    end else if (state == DONE && send_rdy) begin
      next_state = IDLE;
    end

  end

  always_ff @(posedge clk) begin
    $display(" %s|%d %x %x %x %x %x", (state==IDLE ? "IDLE" : state==COMP ? "COMP" : "DONE"), bstage, wc[0][0], wr[0][0], cr[0], dr[0], sine_wave_out[0]);
    if(reset) begin
      state <= IDLE;
      bstage <= 0;
    end else begin
      state <= next_state;
      bstage <= next_bstage;
    end
  end

  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin
      always_ff @(posedge clk) begin
        if(reset) begin
          in_stride[i] <= 0;
          send_msg[i] <= 0;
        end else begin
          if (state == IDLE && recv_val) begin
            in_stride[i][BIT_WIDTH-1:0] <= reversed_msg[i];
          end else if (state == COMP && butterfly_send_val ) begin
            in_stride[i] <= out_butterfly[i];
            if (bstage == max_bstage-1) begin
              send_msg[i] <= out_butterfly[i][BIT_WIDTH-1:0];
            end
          end
        end
      end
    end
  endgenerate

endmodule

`endif
