`default_nettype none
`ifndef fixed_point_combinational_Butterfly
`define fixed_point_combinational_Butterfly
`include "fixed_point/combinational/complex_multiplier.v"

/* Parameterized Combinational butterfly Unit.
 *
 * This modules is a non-buffered version of the butterfly unit and allows
 * multiple butterfly inputs. All computations are combinationsal
 * 
 * Params:
 * - n: bit width 
 * - d: number of decimal bits
 * - b: how many butterflies inputs and outputs this multi-butterfly contains
 * 
 * Inputs:
 *  - ar[], ac[]: real and complex parts of the first number for each butterfly
 *  - br[], bc[]: real and complex parts of the second number for each butterfly
 *  - wr[], wc[]: real and complex parts of the twiddle factor for each butterfly
 *
 * Outputs:
 *  - cr[], cc[]: real and complex parts of the result for each butterfly
 * 
 * Tests: NOT FULLY TESTED
 *  - tests/fixed_point/combinational/butterfly.py [PASSED]
 *
 * Used In:
 *  - Pease FFT Module: fft/pease/fft.v
 *  
 * Author: Barry Lyu.
 * Date: Feb 14th 2024
 */
module fixed_point_combinational_Butterfly #(
  parameter int n = 32,
  parameter int d = 16,
  parameter int b = 4
  // Number of inputs to rotate around
) (
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

  logic [n-1:0] m_cr[b];
  logic [n-1:0] m_cc[b];

  generate
    for (genvar i = 0; i < b; i++) begin
      // complex multiplier instantiation as combinatorial
      fixed_point_combinational_ComplexMultiplierS #(
        .n(n),
        .d(d)
      ) mult (
        .ar(wr[i]),
        .ac(wc[i]),
        .br(br[i]),
        .bc(bc[i]),
        .cr(m_cr[i]),
        .cc(m_cc[i])
      );

      assign cc[i] = ac[i] + m_cc[i];
      assign cr[i] = ar[i] + m_cr[i];
      assign dc[i] = ac[i] - m_cc[i];
      assign dr[i] = ar[i] - m_cr[i];
    end
  endgenerate


endmodule
`endif
