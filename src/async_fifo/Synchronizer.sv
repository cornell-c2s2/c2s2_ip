`ifndef BRGTC6_SYNCHRONIZER
`define BRGTC6_SYNCHRONIZER

//=========================================================================
// Synchronizer
//=========================================================================
//  !!! IMPORTANT: For bit_width > 1, the data needs to be gray coded.
module Synchronizer #(
    parameter p_bit_width = 1
) (
    input   logic                   clk,
    input   logic                   reset,
    input   logic [p_bit_width-1:0]   d,
    output  logic [p_bit_width-1:0]   q
);

    logic [p_bit_width-1:0] s;

    always_ff @(posedge clk) begin
        if (reset) begin
            s <= 0;
            q <= 0;
        end else begin
            s <= d;
            q <= s;
        end
    end

endmodule

`endif /* BRGTC6_SYNCHRONIZER */
