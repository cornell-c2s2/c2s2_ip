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

module FloatCombAdder #(
  parameter int BIT_WIDTH = 32,
  parameter int M_WIDTH   = 23,
  parameter int E_WIDTH   = 8
) (
  input  logic [BIT_WIDTH-1:0] in0,
  input  logic [BIT_WIDTH-1:0] in1,
  output logic [BIT_WIDTH-1:0] out
);
  // Define bit fields
  logic signA, signB, signResult;
  logic [E_WIDTH-1:0] exponentA, exponentB, exponentResult;
  logic [M_WIDTH-1:0] mantissaA, mantissaB, mantissaResult;

  // Extract sign, exponent, and mantissa from inputs A and B
  assign signA = in0[BIT_WIDTH-1];
  assign signB = in1[BIT_WIDTH-1];

  assign exponentA = in0[BIT_WIDTH-2:M_WIDTH];
  assign exponentB = in1[BIT_WIDTH-2:M_WIDTH];

  assign mantissaA = in0[M_WIDTH-1:0];
  assign mantissaB = in1[M_WIDTH-1:0];

  // Compute the difference in exponents
  logic [E_WIDTH-1:0] exponentDiff;
  assign exponentDiff = exponentA - exponentB;

  // Align mantissas based on the exponent difference
  logic [M_WIDTH:0] alignedMantissaA, alignedMantissaB;

  // Align A if B exponent larger
  assign alignedMantissaA = (exponentDiff < 0) ? {1'b1, mantissaA} >> -exponentDiff
      : {1'b1, mantissaA};

  // Shift B if A is larger
  assign alignedMantissaB = (exponentDiff > 0) ? {1'b1, mantissaB} >> exponentDiff
      : {1'b1, mantissaB};

  // Determine the new exponent for the result
  logic [E_WIDTH-1:0] newExponent;
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
  logic [BIT_WIDTH-1:0] intermediateResult;
  logic [BIT_WIDTH-1:0] specialResult;
  logic use_special;

  always_comb begin
    if (isNanA || isNanB) begin  // Result is NaN
      specialResult = (isNanA) ? in0 : in1;
      use_special   = 1'b1;
    end else if (isInfinityA) begin  // A is Infinity
      specialResult = (signA) ? in0 : in1;
      use_special   = 1'b1;
    end else if (isInfinityB) begin  // B is Infinity
      specialResult = (signB) ? in0 : in1;
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
    if (intermediateResult[M_WIDTH+2:M_WIDTH] > 3'b100) begin  // Overflow
      stickyBit = 2'b11;
    end else if ((intermediateResult[M_WIDTH+2:M_WIDTH] == 3'b100) && intermediateResult[22]) begin
      stickyBit = 2'b10;
    end else stickyBit = intermediateResult[M_WIDTH-1:M_WIDTH-2];
  end

  // Round the result
  logic [M_WIDTH+1:0] roundedResult;
  always_comb begin
    if (intermediateResult[M_WIDTH+1:M_WIDTH] == 2'b11) begin  // Round up
      roundedResult = intermediateResult[M_WIDTH:0] + 1;
    end else if (intermediateResult[M_WIDTH+1:M_WIDTH] == 2'b10 && intermediateResult[M_WIDTH-1]) begin // Round to even
      roundedResult = intermediateResult[M_WIDTH:0] + 1;
    end else roundedResult = intermediateResult[M_WIDTH:0];
  end

  // Normalize Mantissa
  logic [M_WIDTH+1:0] normalizedResult;
  always_comb begin
    if (roundedResult[M_WIDTH+1]) begin  // Overflow
      normalizedResult = {roundedResult[M_WIDTH], roundedResult[M_WIDTH-1:0]} >> 1;
    end else if (roundedResult[M_WIDTH:0] == 24'b0) begin  // Underflow
      normalizedResult = {1'b0, roundedResult[M_WIDTH-1:0]} << 1;
    end else normalizedResult = roundedResult;
  end

  // Concatenate sign, exponent, and mantissa to get the result
  always_comb begin
    if (normalizedResult[M_WIDTH+1]) signResult = signA;
    else signResult = signB;

    exponentResult = newExponent;
    mantissaResult = normalizedResult[M_WIDTH:0] + stickyBit;
  end

  logic [BIT_WIDTH-1:0] normalResult;
  assign normalResult = {signResult, exponentResult, mantissaResult};

  // choose between normal output and special output
  cmn_Mux2 #(
    .p_nbits(BIT_WIDTH)
  ) output_mux (
    .in0(normalResult),
    .in1(specialResult),
    .sel(use_special),
    .out(out)
  );

endmodule


`endif
