`ifndef BRGTC6_ASYNC_FIFO
`define BRGTC6_ASYNC_FIFO

`include "async_fifo/Mem1r1w.sv"
`include "async_fifo/WritePtrBlk.sv"
`include "async_fifo/ReadPtrBlk.sv"

//=========================================================================
// Asynchronous FIFO Implementation
//=========================================================================
module AsyncFifo #(
    parameter p_num_entries = 8,
    parameter p_bit_width = 8
)
(
    input   logic                     i_clk,
    input   logic                     o_clk,
    input   logic                     async_rst,

    input   logic [p_bit_width-1:0]   istream_msg,
    input   logic                     istream_val,
    output  logic                     istream_rdy,

    output  logic [p_bit_width-1:0]   ostream_msg,
    output  logic                     ostream_val,
    input   logic                     ostream_rdy
);

    localparam ptr_width = $clog2(p_num_entries) + 1;

    logic full, empty;
    logic [ptr_width-1:0] g_write_ptr;
    logic [ptr_width-1:0] g_read_ptr;

    // verilator lint_off UNUSED
    logic [ptr_width-1:0] b_write_ptr;
    logic [ptr_width-1:0] b_read_ptr;
    // verilator lint_on UNUSED

    Mem1r1w #(
        .p_num_entries(p_num_entries),
        .p_bit_width(p_bit_width)
    ) mem1r1w (
        .clk(i_clk),
        .reset(async_rst),
        .write_en(istream_val && istream_rdy),
        .write_addr(b_write_ptr[ptr_width-2:0]),
        .write_data(istream_msg),
        .read_en(ostream_val),
        .read_addr(b_read_ptr[ptr_width-2:0]),
        .read_data(ostream_msg)
    );

    WritePtrBlk #(
        .p_num_entries(p_num_entries)
    ) write_ptr (
        .g_read_ptr_async(g_read_ptr),
        .clk(i_clk),
        .async_rst(async_rst),
        .w_en(istream_val && istream_rdy),
        .*
    );

    ReadPtrBlk #(
        .p_num_entries(p_num_entries)
    ) read_ptr (
        .g_write_ptr_async(g_write_ptr),
        .clk(o_clk),
        .async_rst(async_rst),
        .r_en(ostream_rdy && ostream_val),
        .*
    );

    assign istream_rdy = !full;
    assign ostream_val = !empty;

endmodule

`endif /* BRGTC6_ASYNC_FIFO */
