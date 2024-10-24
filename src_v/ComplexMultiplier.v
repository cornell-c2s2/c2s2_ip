module fixed_point_combinational_ComplexMultiplier (
	clk,
	reset,
	recv_val,
	recv_rdy,
	send_val,
	send_rdy,
	ar,
	ac,
	br,
	bc,
	cr,
	cc
);
	parameter signed [31:0] n = 32;
	parameter signed [31:0] d = 16;
	parameter signed [31:0] num_mults = 1;
	input wire clk;
	input wire reset;
	input wire recv_val;
	output reg recv_rdy;
	output reg send_val;
	input wire send_rdy;
	input wire [n - 1:0] ar;
	input wire [n - 1:0] ac;
	input wire [n - 1:0] br;
	input wire [n - 1:0] bc;
	output wire [n - 1:0] cr;
	output wire [n - 1:0] cc;
	reg [n - 1:0] c_ar;
	reg [n - 1:0] c_ac;
	reg [n - 1:0] c_br;
	reg [n - 1:0] c_bc;
	reg [n - 1:0] arXbr;
	reg [n - 1:0] acXbc;
	reg [n - 1:0] arcXbrc;
	generate
		if (num_mults == 3) begin : genblk1
			wire [n:1] sv2v_tmp_1272E;
			assign sv2v_tmp_1272E = ar;
			always @(*) c_ar = sv2v_tmp_1272E;
			wire [n:1] sv2v_tmp_AE874;
			assign sv2v_tmp_AE874 = ac;
			always @(*) c_ac = sv2v_tmp_AE874;
			wire [n:1] sv2v_tmp_29444;
			assign sv2v_tmp_29444 = br;
			always @(*) c_br = sv2v_tmp_29444;
			wire [n:1] sv2v_tmp_F85B2;
			assign sv2v_tmp_F85B2 = bc;
			always @(*) c_bc = sv2v_tmp_F85B2;
			wire [n:1] sv2v_tmp_arXbrMult_c;
			always @(*) arXbr = sv2v_tmp_arXbrMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrMult(
				.a(c_ar),
				.b(c_br),
				.c(sv2v_tmp_arXbrMult_c)
			);
			wire [n:1] sv2v_tmp_acXbcMult_c;
			always @(*) acXbc = sv2v_tmp_acXbcMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) acXbcMult(
				.a(c_ac),
				.b(c_bc),
				.c(sv2v_tmp_acXbcMult_c)
			);
			wire [n:1] sv2v_tmp_arXbrcMult_c;
			always @(*) arcXbrc = sv2v_tmp_arXbrcMult_c;
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrcMult(
				.a(c_ar + c_ac),
				.b(c_br + c_bc),
				.c(sv2v_tmp_arXbrcMult_c)
			);
			assign cr = arXbr - acXbc;
			assign cc = (arcXbrc - arXbr) - acXbc;
			wire [1:1] sv2v_tmp_1010E;
			assign sv2v_tmp_1010E = send_rdy;
			always @(*) recv_rdy = sv2v_tmp_1010E;
			wire [1:1] sv2v_tmp_3CA7E;
			assign sv2v_tmp_3CA7E = recv_val;
			always @(*) send_val = sv2v_tmp_3CA7E;
			reg unused = &{clk, reset};
		end
		else if (num_mults == 1) begin : genblk1
			reg [2:0] IDLE = 3'd0;
			reg [2:0] MUL1 = 3'd1;
			reg [2:0] MUL2 = 3'd2;
			reg [2:0] MUL3 = 3'd3;
			reg [2:0] DONE = 3'd4;
			reg [2:0] state;
			reg [2:0] next_state;
			reg [n - 1:0] mul_a;
			reg [n - 1:0] mul_b;
			wire [n - 1:0] mul_c;
			reg unused = &{IDLE, MUL1, MUL2, MUL3, DONE};
			always @(posedge clk)
				if (reset) begin
					state <= IDLE;
					c_ar <= 0;
					c_ac <= 0;
					c_br <= 0;
					c_bc <= 0;
					arXbr <= 0;
					acXbc <= 0;
					arcXbrc <= 0;
				end
				else begin
					state <= next_state;
					if ((state == IDLE) && recv_val) begin
						c_ar <= ar;
						c_ac <= ac;
						c_br <= br;
						c_bc <= bc;
						arXbr <= 0;
						acXbc <= 0;
						arcXbrc <= 0;
					end
					else if (state == MUL1)
						arXbr <= mul_c;
					else if (state == MUL2)
						acXbc <= mul_c;
					else if (state == MUL3)
						arcXbrc <= mul_c;
				end
			always @(*) begin
				next_state = state;
				recv_rdy = 0;
				send_val = 0;
				mul_a = 0;
				mul_b = 0;
				case (state)
					IDLE: begin
						recv_rdy = 1;
						if (recv_val)
							next_state = MUL1;
						else
							next_state = IDLE;
					end
					MUL1: begin
						next_state = MUL2;
						mul_a = c_ar;
						mul_b = c_br;
					end
					MUL2: begin
						next_state = MUL3;
						mul_a = c_ac;
						mul_b = c_bc;
					end
					MUL3: begin
						next_state = DONE;
						mul_a = c_ar + c_ac;
						mul_b = c_br + c_bc;
					end
					DONE: begin
						send_val = 1;
						if (send_rdy)
							next_state = IDLE;
						else
							next_state = state;
					end
					default:
						;
				endcase
			end
			fixed_point_combinational_Multiplier #(
				.n(n),
				.d(d),
				.sign(1)
			) arXbrMult(
				.a(mul_a),
				.b(mul_b),
				.c(mul_c)
			);
			assign cr = arXbr - acXbc;
			assign cc = (arcXbrc - arXbr) - acXbc;
		end
	endgenerate
endmodule
