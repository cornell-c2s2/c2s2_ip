/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/
`define round_near_even   3'b000
`define round_minMag      3'b001
`define round_min         3'b010
`define round_max         3'b011
`define round_near_maxMag 3'b100
`define round_odd         3'b110

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/
`define floatControlWidth 1
`define flControl_tininessBeforeRounding 1'b0
`define flControl_tininessAfterRounding  1'b1

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/
`define flRoundOpt_sigMSBitAlwaysZero  1
`define flRoundOpt_subnormsAlwaysExact 2
`define flRoundOpt_neverUnderflows     4
`define flRoundOpt_neverOverflows      8


module mulRecFN_wrapper#(parameter expWidth = 8, parameter sigWidth = 23)
(
    `ifdef USE_POWER_PINS
        inout vccd1, // User area 1 1.8V supply
        inout vssd1, // User area 1 digital ground
    `endif
    input clk,
    input reset,
    input [(`floatControlWidth - 1):0] control_in,
    input [(expWidth + sigWidth):0] a_in,
    input [(expWidth + sigWidth):0] b_in,
    input [2:0] roundingMode_in,
    output [(expWidth + sigWidth):0] out_out,
    output [4:0] exceptionFlags_out
);


    reg [(`floatControlWidth - 1):0] control;
    reg [(expWidth + sigWidth):0] a, b, out, out_reg, out_reg_2;
    reg [2:0] roundingMode;
    reg [4:0] exceptionFlags, exceptionFlags_reg, exceptionFlags_reg_2;

    always @(posedge clk) begin
        if (reset) begin
            a <= 0;
            b <= 0;
            control <= 0;
            roundingMode <= 0;
            out_reg <= 0;
            exceptionFlags_reg <= 0;
            out_reg_2 <= 0;
            exceptionFlags_reg_2 <= 0;
        end
        else begin
            a <= a_in;
            b <= b_in;
            control <= control_in;
            roundingMode <= roundingMode_in;
            out_reg <= out;
            exceptionFlags_reg <= exceptionFlags;
            out_reg_2 <= out_reg;
            exceptionFlags_reg_2 <= exceptionFlags_reg;
        end
    end

    assign out_out = out_reg_2;
    assign exceptionFlags_out = exceptionFlags_reg_2;

    mulRecFN #(expWidth, sigWidth) mulRecFN_inst (
        .*
    );


endmodule
