//================================================
// Iterative Butterfly Unit
// -----------------------------------------------
// This module performs the butterfly operation
// which is equivalent to the following matrix
// multiplication:
// | 1  w |   | a |   | c |
// | 1 -w | * | b | = | d |
// where w is the ith root of unity e^(-2*pi*i/n)
// and n/d is the fixed point specification`
// This module is used in the FFT module, and
// contains an area optimization parameter to
// save area by not including the complex
// multiplier in certain cases.
//================================================
`default_nettype none
`ifndef FIXED_POINT_MULTI_BUTTERFLY
`define FIXED_POINT_MULTI_BUTTERFLY
`include "src/fixed_point/combinational/complex_multiplier.v"
`include "src/cmn/regs.v"

module FixedPointMultiButterfly #(
  parameter int n = 32,
  parameter int d = 16,
  parameter int b = 4
  // Optimization parameter to save area:
  // 0 if we include the multiplier
  // 1 if omega = 1
  // 2 if omega = -1
  // 3 if omega = i (j)
  // 4 if omega = -i (-j)
) (
  input  logic clk,
  input  logic reset,
  input  logic recv_val,
  output logic recv_rdy,
  output logic send_val,
  input  logic send_rdy,

  input logic [n-1:0] ar[b],
  input logic [n-1:0] ac[b],
  input logic [n-1:0] br[b],
  input logic [n-1:0] bc[b],
  input logic [n-1:0] wr[b],
  input logic [n-1:0] wc[b],

  output logic [n-1:0] cr[b],
  output logic [n-1:0] cc[b],
  output logic [n-1:0] dr[b],
  output logic [n-1:0] dc[b]
);

  /* performs the butterfly operation, equivalent to doing
    | 1  w |   | a |   | c |
    | 1 -w | * | b | = | d |
  */

  // registers for storing the inputs
  logic [n-1:0] s_ar[b];
  logic [n-1:0] s_ac[b];
  logic [n-1:0] s_br[b];
  logic [n-1:0] s_bc[b];
  logic [n-1:0] s_cr[b];
  logic [n-1:0] s_cc[b];
  logic [n-1:0] s_dr[b];
  logic [n-1:0] s_dc[b];
  logic [n-1:0] s_wr[b];
  logic [n-1:0] s_wc[b];

  // state machine registers
  localparam int IDLE = 0;
  localparam int COMP = 1;
  localparam int DONE = 2;
  logic [2:0] state;
  logic [2:0] next_state;
  logic [$clog2(b):0] comp_state;
  logic [$clog2(b):0] next_comp_state;

  // wiring for the complex multipliers
  logic [n-1:0] m_ar;
  logic [n-1:0] m_ac;
  logic [n-1:0] m_br;
  logic [n-1:0] m_bc;
  logic [n-1:0] m_cr;
  logic [n-1:0] m_cc;

  // complex multiplier instantiation as combinatorial
  FixedPointCombComplexMultiplier #(
    .n(n),
    .d(d),
    .num_mults(3) // with 3 mults, can output in same cycle
  ) mult (
    .recv_val(1'b1),
    .recv_rdy(),
    .send_val(),
    .send_rdy(1'b1),
    .clk(clk),
    .reset(reset),
    .ar(m_ar),
    .ac(m_ac),
    .br(m_br),
    .bc(m_bc),
    .cr(m_cr),
    .cc(m_cc)
  );

  // val_rdy logic
  assign recv_rdy = (state == IDLE);
  assign send_val = (state == DONE);

  // registers for storing the inputs / outputs
  genvar i;
  generate
    for(i = 0; i < b; i++) begin: g_loop
      always_ff @(posedge clk) begin
        if(reset) begin
          s_ac[i] <= 0;
          s_ar[i] <= 0;
          s_bc[i] <= 0;
          s_br[i] <= 0;
          s_wr[i] <= 0;
          s_wc[i] <= 0;
        end if(recv_rdy && recv_val) begin
          s_ar[i] <= ar[i];
          s_ac[i] <= ac[i];
          s_br[i] <= br[i];
          s_bc[i] <= bc[i];
          s_wr[i] <= wr[i];
          s_wc[i] <= wc[i];
        end
      end

      assign cr[i] = s_cr[i];
      assign cc[i] = s_cc[i];
      assign dr[i] = s_dr[i];
      assign dc[i] = s_dc[i];
    end
  endgenerate

  // update output storage regs
  always_ff @(posedge clk) begin
    state <= next_state;
    // $display("state: %d", state);
    // $display("comp_state: %d", comp_state);
    // $display("next_comp_state: %d\n", next_comp_state);
    comp_state <= next_comp_state;
    if(state == COMP) begin
      s_cr[comp_state] <= s_ar[comp_state] + m_cr;
      s_cc[comp_state] <= s_ac[comp_state] + m_cc;
      s_dr[comp_state] <= s_ar[comp_state] - m_cr;
      s_dc[comp_state] <= s_ac[comp_state] - m_cc;
    end
  end

  // state transition logic
  always_comb begin
    next_state = state;
    next_comp_state = 0;

    if(reset) begin
      next_state = IDLE;
      next_comp_state = 0;
    end else if (state == IDLE && recv_rdy) begin
      if(recv_val)
        next_state = COMP;
    end else if (state == DONE && send_val) begin
      if(send_rdy)
        next_state = IDLE;
    end else if (state == COMP) begin
      if(comp_state == b-1) begin
        next_state = DONE;
        next_comp_state = 0;
      end else
        next_comp_state = comp_state + 1;
    end

    m_ac = s_bc[comp_state];
    m_ar = s_br[comp_state];
    m_bc = s_wc[comp_state];
    m_br = s_wr[comp_state];
  end
endmodule
`endif