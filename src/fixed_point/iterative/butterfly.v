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
module FixedPointIterativeButterfly
#(
	parameter n = 32,
	parameter d = 16,
	parameter mult = 0
	// Optimization parameter to save area:
	// 0 if we include the multiplier
	// 1 if omega = 1
	// 2 if omega = -1
	// 3 if omega = i (j)
	// 3 if omega = -i (-j)
) (clk, reset, recv_val, recv_rdy, send_val, send_rdy, ar, ac, br, bc, wr, wc, cr, cc, dr, dc);
	/* performs the butterfly operation, equivalent to doing
		| 1  w |   | a |   | c |
		| 1 -w | * | b | = | d |
	*/

	input logic clk, reset;
	input logic recv_val, send_rdy;
	input logic [n-1:0] ar, ac, br, bc, wr, wc;
	output logic send_val, recv_rdy;
	output logic [n-1:0] cr, cc, dr, dc;

	logic [n-1:0] ar_imm, ac_imm;

	logic [n-1:0] tr, tc;

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
	
	cmn_EnResetReg #(n) ac_reg (
        .clk(clk),
        .en(recv_rdy),
        .d(ac),
        .q(ac_imm),
        .reset(reset)
    );
	cmn_EnResetReg #(n) ar_reg (
        .clk(clk),
        .en(recv_rdy),
        .d(ar),
        .q(ar_imm),
        .reset(reset)
    );


	assign cr = ar_imm + tr;
	assign cc = ac_imm + tc;
	assign dr = ar_imm - tr;
	assign dc = ac_imm - tc;
endmodule
`endif