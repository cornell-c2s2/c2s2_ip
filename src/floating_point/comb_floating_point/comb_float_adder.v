//================================================
// comb_float_adder.v
// 
// Combinational floating point multiplier
// Author: Vicky Le (vml37)
// Additional credits: Barry Lyu (fl327), Xilai Dai (xd44)
//================================================

`ifndef COMB_FLOAT_ADDER_V
`define COMB_FLOAT_ADDER_V

module comb_float_adder #(
) (
  input  logic [31:0] a,      // operand A
  input  logic [31:0] b,      // operand B
  output logic [31:0] result  // Result of the addition
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
  logic [24:0] intermediateResult;
  always_comb begin
    if (isNanA || isNanB)  // Result is NaN
      result = (isNanA) ? a : b;
    else if (isInfinityA)  // A is Infinity
      result = (signA) ? a : b;
    else if (isInfinityB)  // B is Infinity
      result = (signB) ? a : b;
    else if (signA == signB)  // Both operands have the same sign
      intermediateResult = alignedMantissaA + alignedMantissaB;
    else if (signA == 1)  // Operand A is negative
      intermediateResult = alignedMantissaB - alignedMantissaA;
    else  // Operand B is negative
      intermediateResult = alignedMantissaA - alignedMantissaB;
  end

  // Handle the case when intermediate result overflows
  logic [1:0] stickyBit;
  always_comb begin
    if (intermediateResult[25:23] > 3'b100) begin  // Overflow
      stickyBit = 2'b11;
    end else if (intermediateResult[25:23] == 3'b100 && intermediateResult[22]) begin
      stickyBit = 2'b10;
    end else stickyBit = intermediateResult[22:21];
  end

  // Round the result
  logic [24:0] roundedResult;
  always_comb begin
    if (intermediateResult[24:23] == 2'b11)  // Round up
      roundedResult = intermediateResult[23:0] + 1;
    else if (intermediateResult[24:23] == 2'b10 && intermediateResult[22])  // Round to even
      roundedResult = intermediateResult[23:0] + 1;
    else roundedResult = intermediateResult[23:0];
  end

  // Re-normalize the mantissa if necessary
  logic [24:0] normalizedResult;
  always_comb begin
    if (roundedResult[24])  // Overflow
      normalizedResult = {roundedResult[23], roundedResult[22:0]} >> 1;
    else if (roundedResult[23:0] == 24'b0)  // Underflow
      normalizedResult = {1'b0, roundedResult[22:0]} << 1;
    else normalizedResult = roundedResult;
  end

  // Concatenate sign, exponent, and mantissa to get the result
  always_comb begin
    if (normalizedResult[24]) signResult = signA;
    else signResult = signB;

    exponentResult = newExponent;
    mantissaResult = normalizedResult[23:0] + stickyBit;
  end

  assign result = {signResult, exponentResult, mantissaResult};

endmodule


`endif
