//================================================
// comb_float_adder.v
// 
// Combinational floating point multiplier
// Author: Vicky Le (vml37)
// Additional credits: Barry Lyu (fl327), Xilai Dai (xd44)
//================================================

`ifndef COMB_FLOAT_ADDER
`define COMB_FLOAT_ADDER

module Comb_float_adder #(
  parameter int BIT_WIDTH = 32
) (
  input logic reset,
  input logic clk,

  input  logic [2 * BIT_WIDTH - 1:0] recv_msg,
  input  logic                       recv_val,
  output logic                       recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic                   send_val,
  input  logic                   send_rdy
);
  logic [BIT_WIDTH-1:0] a;  // operand A
  logic [BIT_WIDTH-1:0] b;  // operand B

  // Define operands a and b
  assign a = recv_msg[2*BIT_WIDTH-1:BIT_WIDTH];
  assign b = recv_msg[BIT_WIDTH-1:0];

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

  // Normalize Mantissa
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

  assign send_msg = {signResult, exponentResult, mantissaResult};

  // val-rdy logic
  logic [1:0] currentState;
  logic [1:0] nextState;
  logic [1:0] IDLE = 2'd0, CALC = 2'd1, DONE = 2'd3;

  // Next State Comb Logic
  always_comb begin
    case (currentState)
      IDLE:    if (recv_val && recv_rdy) nextState = CALC;
               else nextState = IDLE;
      CALC:    if (i == 1) nextState = DONE;
               else nextState = CALC;
      DONE:    if (send_rdy && send_val) nextState = IDLE;
               else nextState = DONE;
      default: nextState = IDLE;
    endcase
  end

  // State FFs
  always_ff @(posedge clk) begin
    if (reset) begin
      currentState <= IDLE;
    end else begin
      currentState <= nextState;
    end
  end

  // Counter logic
  always_ff @(posedge clk) begin
    case (currentState)
      IDLE: i <= 0;
      CALC: i <= i + 1;
      default: i <= i;
    endcase
  end

endmodule


`endif
