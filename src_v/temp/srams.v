module cmn_CombinationalBitSRAM_1rw (
	clk,
	reset,
	read_en,
	read_addr,
	read_data,
	write_en,
	write_addr,
	write_data
);
	parameter p_data_nbits = 1;
	parameter p_num_entries = 2;
	parameter c_addr_nbits = $clog2(p_num_entries);
	input wire clk;
	input wire reset;
	input wire read_en;
	input wire [c_addr_nbits - 1:0] read_addr;
	output reg [p_data_nbits - 1:0] read_data;
	input wire write_en;
	input wire [c_addr_nbits - 1:0] write_addr;
	input wire [p_data_nbits - 1:0] write_data;
	reg [p_data_nbits - 1:0] mem [p_num_entries - 1:0];
	always @(*)
		if (read_en)
			read_data = mem[read_addr];
		else
			read_data = 'hx;
	always @(posedge clk)
		if (write_en)
			mem[write_addr] = write_data;
endmodule
module cmn_CombinationalSRAM_1rw (
	clk,
	reset,
	read_en,
	read_addr,
	read_data,
	write_en,
	write_byte_en,
	write_addr,
	write_data
);
	parameter p_data_nbits = 1;
	parameter p_num_entries = 2;
	parameter c_addr_nbits = $clog2(p_num_entries);
	parameter c_data_nbytes = (p_data_nbits + 7) / 8;
	input wire clk;
	input wire reset;
	input wire read_en;
	input wire [c_addr_nbits - 1:0] read_addr;
	output reg [p_data_nbits - 1:0] read_data;
	input wire write_en;
	input wire [c_data_nbytes - 1:0] write_byte_en;
	input wire [c_addr_nbits - 1:0] write_addr;
	input wire [p_data_nbits - 1:0] write_data;
	reg [p_data_nbits - 1:0] mem [p_num_entries - 1:0];
	always @(*)
		if (read_en)
			read_data = mem[read_addr];
		else
			read_data = 'hx;
	genvar i;
	generate
		for (i = 0; i < c_data_nbytes; i = i + 1) begin : test
			always @(posedge clk)
				if (write_en && write_byte_en[i])
					mem[write_addr][((i + 1) * 8) - 1:i * 8] <= write_data[((i + 1) * 8) - 1:i * 8];
		end
	endgenerate
endmodule
module cmn_SynchronousSRAM_1rw (
	clk,
	reset,
	read_en,
	read_addr,
	read_data,
	write_en,
	write_byte_en,
	write_addr,
	write_data
);
	parameter p_data_nbits = 1;
	parameter p_num_entries = 2;
	parameter c_addr_nbits = $clog2(p_num_entries);
	parameter c_data_nbytes = (p_data_nbits + 7) / 8;
	input wire clk;
	input wire reset;
	input wire read_en;
	input wire [c_addr_nbits - 1:0] read_addr;
	output reg [p_data_nbits - 1:0] read_data;
	input wire write_en;
	input wire [c_data_nbytes - 1:0] write_byte_en;
	input wire [c_addr_nbits - 1:0] write_addr;
	input wire [p_data_nbits - 1:0] write_data;
	reg [p_data_nbits - 1:0] mem [p_num_entries - 1:0];
	always @(posedge clk)
		if (read_en)
			read_data <= mem[read_addr];
		else
			read_data <= 'hx;
	genvar i;
	generate
		for (i = 0; i < c_data_nbytes; i = i + 1) begin : test
			always @(posedge clk)
				if (write_en && write_byte_en[i])
					mem[write_addr][((i + 1) * 8) - 1:i * 8] <= write_data[((i + 1) * 8) - 1:i * 8];
		end
	endgenerate
endmodule
