module cmn_Trace (
	clk,
	reset
);
	input wire clk;
	input wire reset;
	integer len0;
	integer len1;
	integer idx0;
	integer idx1;
	localparam nchars = 512;
	localparam nbits = 4096;
	wire [4095:0] storage;
	integer cycles_next = 0;
	integer cycles = 0;
	reg [3:0] level;
	initial if (!$value$plusargs("trace=%d", level))
		level = 0;
	always @(posedge clk) cycles <= (reset ? 0 : cycles_next);
	task append_str;
		output reg [4095:0] trace;
		input reg [4095:0] str;
		begin
			len0 = 1;
			while (str[len0 * 8+:8] != 0) len0 = len0 + 1;
			idx0 = trace[31:0];
			for (idx1 = len0 - 1; idx1 >= 0; idx1 = idx1 - 1)
				begin
					trace[idx0 * 8+:8] = str[idx1 * 8+:8];
					idx0 = idx0 - 1;
				end
			trace[31:0] = idx0;
		end
	endtask
	task append_str_ljust;
		output reg [4095:0] trace;
		input reg [4095:0] str;
		begin
			idx0 = trace[31:0];
			idx1 = nchars;
			while (str[(idx1 * 8) - 1-:8] != 0) begin
				trace[idx0 * 8+:8] = str[(idx1 * 8) - 1-:8];
				idx0 = idx0 - 1;
				idx1 = idx1 - 1;
			end
			trace[31:0] = idx0;
		end
	endtask
	task append_chars;
		output reg [4095:0] trace;
		input reg [7:0] char;
		input integer num;
		begin
			idx0 = trace[31:0];
			for (idx1 = 0; idx1 < num; idx1 = idx1 + 1)
				begin
					trace[idx0 * 8+:8] = char;
					idx0 = idx0 - 1;
				end
			trace[31:0] = idx0;
		end
	endtask
	task append_val_str;
		output reg [4095:0] trace;
		input reg val;
		input reg [4095:0] str;
		begin
			len1 = 0;
			while (str[len1 * 8+:8] != 0) len1 = len1 + 1;
			if (val)
				append_str(trace, str);
			else if (!val)
				append_chars(trace, " ", len1);
			else begin
				append_str(trace, "x");
				append_chars(trace, " ", len1 - 1);
			end
		end
	endtask
	task append_val_rdy_str;
		output reg [4095:0] trace;
		input reg val;
		input reg rdy;
		input reg [4095:0] str;
		begin
			len1 = 0;
			while (str[len1 * 8+:8] != 0) len1 = len1 + 1;
			if (rdy && val)
				append_str(trace, str);
			else if (rdy && !val)
				append_chars(trace, " ", len1);
			else if (!rdy && val) begin
				append_str(trace, "#");
				append_chars(trace, " ", len1 - 1);
			end
			else if (!rdy && !val) begin
				append_str(trace, ".");
				append_chars(trace, " ", len1 - 1);
			end
			else begin
				append_str(trace, "x");
				append_chars(trace, " ", len1 - 1);
			end
		end
	endtask
endmodule
