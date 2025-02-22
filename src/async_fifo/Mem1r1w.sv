`ifndef BRGTC6_MEM_1R1W_SV
`define BRGTC6_MEM_1R1W_SV

//=========================================================================
// Memory with 1 Read and 1 Write Port
//=========================================================================
module Mem1r1w #(
    parameter p_num_entries = 8,
    parameter p_bit_width = 5,
    parameter p_addr_width = $clog2(p_num_entries)
)
(
    input   logic                     clk,
    input   logic                     reset,
    input   logic                     write_en,
    input   logic [p_addr_width-1:0]  write_addr,
    input   logic [ p_bit_width-1:0]  write_data,
    input   logic                     read_en,
    input   logic [p_addr_width-1:0]  read_addr,
    output  logic [ p_bit_width-1:0]  read_data
);

    logic [p_bit_width-1:0] mem [p_num_entries-1:0];

    always_ff @(posedge clk) begin
        if (write_en & ~reset) begin
            mem[int'(write_addr)] <= write_data;
        end
    end

    assign read_data = mem[int'(read_addr)] & {p_bit_width{read_en}};

endmodule

`endif /* BRGTC6_MEM_1R1W_SV */
