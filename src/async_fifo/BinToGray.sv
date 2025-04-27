`ifndef BRGTC6_BIN_TO_GRAY
`define BRGTC6_BIN_TO_GRAY

//=========================================================================
// Binary to Gray Code Converter
//=========================================================================
module BinToGray #(
    parameter p_bit_width = 3
) (
    input   logic [p_bit_width-1:0]   bin,
    output  logic [p_bit_width-1:0]   gray
);
    assign gray = bin ^ (bin >> 1);
endmodule

`endif /* BRGTC6_BIN_TO_GRAY */

