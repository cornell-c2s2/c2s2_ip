//================================================
// Iterative Butterfly Unit
// -----------------------------------------------
// This module performs the butterfly operation
// which is equivalent to the following matrix
// multiplication:
// | 1  w |   | a |   | c |
// | 1 -w | * | b | = | d |
// where w is the ith root of unity e^(-2*pi*i/n)
// and n/d is the fixed point specification.
// This module is used in the FFT module, and
// contains an area optimization parameter to
// save area by not including the complex
// multiplier in certain cases.
//================================================
`default_nettype none
`ifndef FIXED_POINT_ITERATIVE_BUTTERFLY
`define PROJECT_BUTTERFLY_V
`include "src/fixed_point/iterative/complex_multiplier.v"
`include "src/cmn/regs.v"

module FixedPointIterativeButterfly #(
  parameter int n = 32,
  parameter int d = 16,
  parameter byte mult = 0
  // Optimization parameter to save area:
  // 0 if we include the multiplier
  // 1 if omega = 1
  // 2 if omega = -1
  // 3 if omega = i (j)
  // 4 if omega = -i (-j)
) (
  input logic clk,
  input logic reset,
  input logic recv_val,
  output logic recv_rdy,
  output logic send_val,
  input logic send_rdy,
  
  input logic [n-1:0] ar,
  input logic [n-1:0] ac,
  input logic [n-1:0] br,
  input logic [n-1:0] bc,
  input logic [n-1:0] wr,
  input logic [n-1:0] wc, 
  
  output logic [n-1:0] cr,
  output logic [n-1:0] cc,
  output logic [n-1:0] dr,
  output logic [n-1:0] dc
);
  /* performs the butterfly operation, equivalent to doing
    | 1  w |   | a |   | c |
    | 1 -w | * | b | = | d |
  */
  logic [n-1:0] ar_imm, ac_imm;
  logic [n-1:0] tr, tc;

  case (mult)
    1: begin: l_omega_1
      always_ff @(posedge clk) begin
        if (reset) begin
          cr <= 0; cc <= 0; dr <= 0; dc <= 0;
          send_val <= 0;
        end else if (recv_val & recv_rdy) begin
          cr <= ar + br; cc <= ac + bc; dr <= ar - br; dc <= ac - bc;
          send_val <= 1;
        end else if (send_val & send_rdy) begin
          send_val <= 0;
        end else begin
          cr <= cr; cc <= cc; dr <= dr; dc <= dc;
          send_val <= send_val;
        end
      end
      assign recv_rdy = ~send_val;
    end
    2: begin: l_omega_neg_1
      always_ff @(posedge clk) begin
        if (reset) begin
          cr <= 0; cc <= 0; dr <= 0; dc <= 0;
          send_val <= 0;
        end else if (recv_val & recv_rdy) begin
          cr <= ar - br; cc <= ac - bc; dr <= ar + br; dc <= ac + bc;
          send_val <= 1;
        end else if (send_val & send_rdy) begin
          send_val <= 0;
        end else begin
          cr <= cr; cc <= cc; dr <= dr; dc <= dc;
          send_val <= send_val;
        end
      end
      assign recv_rdy = ~send_val;
    end
    3: begin: l_omega_i
      always_ff @(posedge clk) begin
        if (reset) begin
          cr <= 0; cc <= 0; dr <= 0; dc <= 0;
          send_val <= 0;
        end else if (recv_val & recv_rdy) begin
          cr <= ar - bc; cc <= ac + br; dr <= ar + bc; dc <= ac - br;
          send_val <= 1;
        end else if (send_val & send_rdy) begin
          send_val <= 0;
        end else begin
          cr <= cr; cc <= cc; dr <= dr; dc <= dc;
          send_val <= send_val;
        end
      end
      assign recv_rdy = ~send_val;
    end
    4: begin: l_omega_neg_i
      always_ff @(posedge clk) begin
        if (reset) begin
          cr <= 0; cc <= 0; dr <= 0; dc <= 0;
          send_val <= 0;
        end else if (recv_val & recv_rdy) begin
          cr <= ar + bc; cc <= ac - br; dr <= ar - bc; dc <= ac + br;
          send_val <= 1;
        end else if (send_val & send_rdy) begin
          send_val <= 0;
        end else begin
          cr <= cr; cc <= cc; dr <= dr; dc <= dc;
          send_val <= send_val;
        end
      end
      assign recv_rdy = ~send_val;
    end
    default: begin: l_no_omega
      FixedPointIterativeComplexMultiplier #(.n(n), .d(d)) mul ( // ar * br
        .clk(clk),
        .reset(reset),
        .ar(br),
        .ac(bc),
        .br(wr),
        .bc(wc),
        .cr(tr),
        .cc(tc),
        .recv_val(recv_val),
        .recv_rdy(recv_rdy),
        .send_val(send_val),
        .send_rdy(send_rdy)
      );
      cmn_EnResetReg #(n) ac_reg(.clk(clk), .en(recv_rdy), .d(ac), .q(ac_imm), .reset(reset)); 
      cmn_EnResetReg #(n) ar_reg(.clk(clk), .en(recv_rdy), .d(ar), .q(ar_imm), .reset(reset));

      assign cr = ar_imm + tr;
      assign cc = ac_imm + tc;
      assign dr = ar_imm - tr;
      assign dc = ac_imm - tc;
    end
  endcase
endmodule
`endif