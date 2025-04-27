`ifndef BRGTC6_READ_PTR_BLK
`define BRGTC6_READ_PTR_BLK

`include "async_fifo/Synchronizer.sv"
`include "async_fifo/BinToGray.sv"
`include "async_fifo/ResetSync.sv"

//=========================================================================
// Read Pointer Handler Block
//=========================================================================
module ReadPtrBlk #(
    parameter p_num_entries = 8,
    parameter p_ptr_width = $clog2(p_num_entries) + 1 // Extra bit for wrap around
)
(
    input   logic                     clk,
    input   logic                     async_rst,

    output  logic [p_ptr_width-1:0]   b_read_ptr,
    output  logic [p_ptr_width-1:0]   g_read_ptr,

    input   logic [p_ptr_width-1:0]   g_write_ptr_async,
    input   logic                     r_en,
    output  logic                     empty
);

    logic reset;

    ResetSync reset_sync (
        .clk(clk),
        .async_rst(async_rst),
        .reset(reset)
    );

    logic [p_ptr_width-1:0] g_write_ptr;

    Synchronizer #(
        .p_bit_width(p_ptr_width)
    ) synch (
        .clk(clk),
        .reset(reset),
        .d(g_write_ptr_async),
        .q(g_write_ptr)
    );

    logic [p_ptr_width-1:0] b_read_ptr_next;
    logic [p_ptr_width-1:0] g_read_ptr_next;

    assign b_read_ptr_next = b_read_ptr + {{(p_ptr_width-1){1'b0}},(r_en && !empty)};

    BinToGray #(
        .p_bit_width(p_ptr_width)
    ) bin_to_gray (
        .bin(b_read_ptr_next),
        .gray(g_read_ptr_next)
    );
        
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            b_read_ptr <= 0;
            g_read_ptr <= 0;
        end 
        else begin
            b_read_ptr <= b_read_ptr_next;
            g_read_ptr <= g_read_ptr_next;
        end 
    end

    assign empty = reset || (g_read_ptr == g_write_ptr);
endmodule

`endif /* BRGTC6_READ_PTR_BLK */
