
`ifndef FIXED_POINT_FFT
`define FIXED_POINT_FFT

`include "fft/cooley_tukey/helpers/sine_wave.v"
`include "fft/cooley_tukey/helpers/bit_reverse.v"
`include "cmn/trace.v"

//`include "fixed_point/combinational/butterflyAlt.v"

`include "fixed_point/combinational/butterfly.v"

`include "fft/pease/helpers/stride_permutation.v"
`include "fft/pease/helpers/twiddle_generator.v"
`include "serdes/deserializer.v"
`include "serdes/serializer.v"

module fft_pease_FFT #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg,
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic                   send_val,
  input  logic                   send_rdy,

  input logic reset,
  input logic clk
);

  logic fft_recv_rdy, fft_recv_val;
  logic [BIT_WIDTH - 1:0] fft_recv_msg[N_SAMPLES - 1:0];

  logic fft_send_rdy, fft_send_val;
  logic [BIT_WIDTH - 1:0] fft_send_msg[N_SAMPLES - 1:0];

  serdes_Deserializer #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) deser (
    .send_val(fft_recv_val),
    .send_rdy(fft_recv_rdy),
    .send_msg(fft_recv_msg),
    .*
  );

  fft_pease_FFT_main #(
    .BIT_WIDTH (BIT_WIDTH),
    .N_SAMPLES (N_SAMPLES),
    .DECIMAL_PT(DECIMAL_PT)
  ) fft (
    .recv_msg(fft_recv_msg),
    .recv_val(fft_recv_val),
    .recv_rdy(fft_recv_rdy),

    .send_msg(fft_send_msg),
    .send_val(fft_send_val),
    .send_rdy(fft_send_rdy),
    .*
  );

  serdes_Serializer #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) ser (
    .recv_val(fft_send_val),
    .recv_rdy(fft_send_rdy),
    .recv_msg(fft_send_msg),
    .*
  );

endmodule

module fft_pease_FFT_main #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES-1:0],
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES-1:0],
  output logic                   send_val,
  input  logic                   send_rdy,

  input logic reset,
  input logic clk
);

  logic [2:0] IDLE = 3'd0, COMP = 3'd1, DONE = 3'd2;

  localparam int BstageBits = (N_SAMPLES > 2) ? $clog2($clog2(N_SAMPLES)) : 1;
  localparam int log = $clog2(N_SAMPLES) - 1;
  logic [BstageBits-1:0] max_bstage = log[BstageBits-1:0];

  logic [2:0] state;
  logic [2:0] next_state;

  assign recv_rdy = (state == IDLE);
  assign send_val = (state == DONE);

  logic [     BstageBits-1:0] bstage;
  logic [     BstageBits-1:0] next_bstage;

  logic [2 * BIT_WIDTH - 1:0] out_stride   [N_SAMPLES - 1:0];
  logic [2 * BIT_WIDTH - 1:0] in_butterfly [N_SAMPLES - 1:0];
  logic [2 * BIT_WIDTH - 1:0] out_butterfly[N_SAMPLES - 1:0];

  logic [    BIT_WIDTH - 1:0] reversed_msg [N_SAMPLES - 1:0];
  fft_cooley_tukey_helpers_BitReverse #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) bit_reverse (
    .in (recv_msg),
    .out(reversed_msg)
  );

  fft_pease_helpers_StridePermutation #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH * 2)
  ) stride_permutation (
    .recv(out_butterfly),
    .send(out_stride)
  );

  logic [BIT_WIDTH - 1:0] sine_wave_out[      0:N_SAMPLES - 1];
  logic [BIT_WIDTH - 1:0] wr_pre       [$clog2(N_SAMPLES)-1:0] [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] wc_pre       [$clog2(N_SAMPLES)-1:0] [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] wr           [$clog2(N_SAMPLES)-1:0] [N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] wc           [$clog2(N_SAMPLES)-1:0] [N_SAMPLES/2 - 1:0];

  generate
    for (genvar i = 0; i < $clog2(N_SAMPLES); i++) begin
      fft_pease_helpers_TwiddleGenerator #(
        .BIT_WIDTH (BIT_WIDTH),
        .DECIMAL_PT(DECIMAL_PT),
        .SIZE_FFT  (N_SAMPLES),
        .STAGE_FFT (i)
      ) twiddle_generator (
        .sine_wave_in(sine_wave_out),
        .twiddle_real(wr[i]),
        .twiddle_imaginary(wc[i])
      );

      // for (genvar b = 0; b < N_SAMPLES / 2; b++) begin
      //   assign wr[i][b] = wr_pre[i][b];
      //   assign wc[i][b] = wc_pre[i][b];
      //   //end
      // end
    end
  endgenerate

  fft_cooley_tukey_helpers_SineWave #(
    .N(N_SAMPLES),
    .W(BIT_WIDTH),
    .D(DECIMAL_PT)
  ) sine_wave (
    .sine_wave_out(sine_wave_out)
  );


  logic [BIT_WIDTH - 1:0] ar[N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] ac[N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] br[N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] bc[N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] cr[N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] cc[N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] dr[N_SAMPLES/2 - 1:0];
  logic [BIT_WIDTH - 1:0] dc[N_SAMPLES/2 - 1:0];

  generate
    for (genvar i = 0; i < N_SAMPLES / 2; i++) begin
      assign ar[i] = in_butterfly[i*2][BIT_WIDTH-1:0];
      assign ac[i] = in_butterfly[i*2][2*BIT_WIDTH-1:BIT_WIDTH];
      assign br[i] = in_butterfly[i*2+1][BIT_WIDTH-1:0];
      assign bc[i] = in_butterfly[i*2+1][2*BIT_WIDTH-1:BIT_WIDTH];
      assign out_butterfly[i*2][BIT_WIDTH-1:0] = cr[i];
      assign out_butterfly[i*2][2*BIT_WIDTH-1:BIT_WIDTH] = cc[i];
      assign out_butterfly[i*2+1][BIT_WIDTH-1:0] = dr[i];
      assign out_butterfly[i*2+1][2*BIT_WIDTH-1:BIT_WIDTH] = dc[i];
    end
  endgenerate

  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin
      assign send_msg[i] = in_butterfly[i][BIT_WIDTH-1:0];
    end
  endgenerate

  logic btfy_recv_val, btfy_recv_rdy, btfy_send_val;
  assign btfy_recv_val = state == COMP;

  fixed_point_combinational_FixedPointMultiButterfly #(
    .n(BIT_WIDTH),
    .d(DECIMAL_PT),
    .b(N_SAMPLES / 2),
    .num_mults(2)
  ) fft_stage (
    .recv_val(btfy_recv_val),
    .recv_rdy(btfy_recv_rdy),
    .send_val(btfy_send_val),
    .send_rdy(1'b1),
    .wr(wr[bstage]),
    .wc(wc[bstage]),
    .*
  );

  // fixed_point_combinational_Butterfly #(
  //   .n(BIT_WIDTH),
  //   .d(DECIMAL_PT),
  //   .b(N_SAMPLES / 2)
  // ) fft_stage (
  //   .wr(wr[bstage]),
  //   .wc(wc[bstage]),
  //   .*
  // );

  always_comb begin
    next_state  = state;
    next_bstage = bstage;
    if (state == IDLE && recv_val) begin
      next_state = COMP;
    end else begin
      if (state == COMP) begin
        if (bstage == max_bstage && btfy_send_val) begin
          next_state  = DONE;
          next_bstage = 0;
        end else begin
          //next_bstage = bstage + 1;
          next_bstage = bstage + btfy_send_val;
        end
      end else begin
        if (state == DONE && send_rdy) begin
          next_state = IDLE;
        end else begin
        end
      end
    end

  end

  always_ff @(posedge clk) begin
    if (reset) begin
      state  <= IDLE;
      bstage <= 0;
    end else begin
      state  <= next_state;
      bstage <= next_bstage;
    end
    //$display("btfy_send_val: %b", btfy_send_val, " bstage: %d", bstage, " maxbstage: %d",
    //         max_bstage, " state: %d", state, " next_state: %d", next_state);
  end

  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin
      always_ff @(posedge clk) begin
        if (reset) begin
          in_butterfly[i] <= 0;
          //send_msg[i] <= 0;
        end else begin
          if (state == IDLE && recv_val) begin
            in_butterfly[i][BIT_WIDTH-1:0] <= reversed_msg[i];
            in_butterfly[i][2*BIT_WIDTH-1:BIT_WIDTH] <= 0;
          end else begin
            if (state == COMP && btfy_send_val) begin
              in_butterfly[i] <= out_stride[i];
            end else begin
            end
          end
        end
      end
    end
  endgenerate

  //----------------------------------------------------------------------
  // Line Tracing
  //----------------------------------------------------------------------

`ifndef SYNTHESIS

  logic [`CMN_TRACE_NBITS-1:0] str;
  `CMN_TRACE_BEGIN
  begin

    // $sformat( str, "%x", istream_msg );
    // cmn_trace.append_val_rdy_str(
    //     trace_str, istream_val, istream_rdy, str
    // ); 
    cmn_trace.append_str(
        trace_str, "("
    ); cmn_trace.append_str(
        trace_str, ")"
    );

    // $sformat( str, "%x", ostream_msg );
    // cmn_trace.append_val_rdy_str(
    //     trace_str, ostream_val, ostream_rdy, str
    // );

  end
  `CMN_TRACE_END

`endif

endmodule

`endif

