//================================================
// comb_float_adder.v
// 
// Combinational floating point multiplier
// Author: Vicky Le (vml37)
// Additional credits: Barry Lyu (fl327), Xilai Dai (xd44)
//================================================

`ifndef COMB_FLOAT_ADDER_V
`define COMB_FLOAT_ADDER_V

`include "src/cmn/muxes.v"

module CombFloatAdder #(
  parameter int BIT_WIDTH = 32
) (
  input  logic [31:0] a,
  input  logic [31:0] b,
  output logic [31:0] out
);
  // Define bit fields
  logic signA, signB, signResult;
  logic [7:0] exponentA, exponentB, exponentResult;
  logic [22:0] mantissaA, mantissaB, mantissaResult;

  // Extract sign, exponent, and mantissa from inputs A and B
  assign signA = a[31];
  assign signB = b[31];

  assign exponentA = a[30:23];
  assign exponentB = b[30:23];

  assign mantissaA = a[22:0];
  assign mantissaB = b[22:0];

  // Compute the difference in exponents
  logic [7:0] exponentDiff;
  assign exponentDiff = exponentA - exponentB;

  // Align mantissas based on the exponent difference
  logic [23:0] alignedMantissaA, alignedMantissaB;

  // Align A if B exponent larger
  assign alignedMantissaA = (exponentDiff < 0) ? {1'b1, mantissaA} >> -exponentDiff
      : {1'b1, mantissaA};

  // Shift B if A is larger
  assign alignedMantissaB = (exponentDiff > 0) ? {1'b1, mantissaB} >> exponentDiff
      : {1'b1, mantissaB};

  // Determine the new exponent for the result
  logic [7:0] newExponent;
  always_comb begin
    if (exponentDiff > 0) begin
      // Adjust for exponent difference
      newExponent = exponentB + exponentDiff;
    end else begin
      // Adjust for exponent difference
      newExponent = exponentA + exponentDiff;
    end
  end

  // check if infinity or Not a number
  logic isInfinityA, isInfinityB, isNanA, isNanB;
  assign isInfinityA = (exponentA == 8'hFF) && (mantissaA == 23'h0);
  assign isInfinityB = (exponentB == 8'hFF) && (mantissaB == 23'h0);

  assign isNanA = (exponentA == 8'hFF) && (mantissaA != 23'h0);
  assign isNanB = (exponentB == 8'hFF) && (mantissaB != 23'h0);

  // Do fixed point addition accounting for NaN and Infinity
  logic [31:0] intermediateResult;
  logic use_special;
  logic [31:0] specialResult;

  always_comb begin
    if (isNanA || isNanB) begin  // Result is NaN
      specialResult = (isNanA) ? a : b;
      use_special   = 1'b1;
    end else if (isInfinityA) begin  // A is Infinity
      specialResult = (signA) ? a : b;
      use_special   = 1'b1;
    end else if (isInfinityB) begin  // B is Infinity
      specialResult = (signB) ? a : b;
      use_special   = 1'b1;
    end else if (signA == signB) begin  // Both operands have the same sign
      intermediateResult = alignedMantissaA + alignedMantissaB;
    end else if (signA == 1) begin  // Operand A is negative
      intermediateResult = alignedMantissaB - alignedMantissaA;
    end else  // Operand B is negative
      intermediateResult = alignedMantissaA - alignedMantissaB;
  end

  // Handle the case when intermediate result overflows
  logic [1:0] stickyBit;
  always_comb begin
    if (intermediateResult[25:23] > 3'b100) begin  // Overflow
      stickyBit = 2'b11;
    end else if ((intermediateResult[25:23] == 3'b100) && intermediateResult[22]) begin
      stickyBit = 2'b10;
    end else stickyBit = intermediateResult[22:21];
  end

  // Round the result
  logic [24:0] roundedResult;
  always_comb begin
    if (intermediateResult[24:23] == 2'b11) begin  // Round up
      roundedResult = intermediateResult[23:0] + 1;
    end else if (intermediateResult[24:23] == 2'b10 && intermediateResult[22]) begin // Round to even
      roundedResult = intermediateResult[23:0] + 1;
    end else roundedResult = intermediateResult[23:0];
  end

  // Normalize Mantissa
  logic [24:0] normalizedResult;
  always_comb begin
    if (roundedResult[24]) begin  // Overflow
      normalizedResult = {roundedResult[23], roundedResult[22:0]} >> 1;
    end else if (roundedResult[23:0] == 24'b0) begin  // Underflow
      normalizedResult = {1'b0, roundedResult[22:0]} << 1;
    end else normalizedResult = roundedResult;
  end

  // Concatenate sign, exponent, and mantissa to get the result
  always_comb begin
    if (normalizedResult[24]) signResult = signA;
    else signResult = signB;

    exponentResult = newExponent;
    mantissaResult = normalizedResult[23:0] + stickyBit;
  end

  logic [31:0] normalResult;
  assign normalResult = {signResult, exponentResult, mantissaResult};

  // choose between normal output and special output
  cmn_Mux2 #(
    .p_nbits(32)
  ) output_mux (
    .in0(normalResult),
    .in1(specialResult),
    .sel(use_special),
    .out(out)
  );

endmodule


`endif
