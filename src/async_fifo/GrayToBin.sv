`ifndef BRGTC6_GRAY_TO_BIN
`define BRGTC6_GRAY_TO_BIN

//=========================================================================
// Gray Code to Binary Converter
//=========================================================================
module GrayToBin #(
    parameter p_bit_width = 3
) (
    input   logic [p_bit_width-1:0]   gray,
    output  logic [p_bit_width-1:0]   bin
);
    genvar i;
    generate
        for(i=0; i < p_bit_width; i++) begin : l_gen_loop
            assign bin[i] = ^(gray >> i);
        end
    endgenerate

endmodule

`endif /* BRGTC6_GRAY_TO_BIN */
