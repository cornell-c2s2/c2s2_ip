//================================================
// Iterative Multiplier
// --------------------
// Unpipelined fixed point iterative multiplier
// using Val/Rdy interface. This is a simple
// unpipelined multiplier that takes `n` cycles
// to complete a multiplication.
//================================================
`default_nettype none



//========================================================================
// Verilog Components: Muxes
//========================================================================




//------------------------------------------------------------------------
// 2 Input Mux
//------------------------------------------------------------------------

module cmn_Mux2 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  input  logic               sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      1'd0: out = in0;
      1'd1: out = in1;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 3 Input Mux
//------------------------------------------------------------------------

module cmn_Mux3 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  input  logic [        1:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      2'd0: out = in0;
      2'd1: out = in1;
      2'd2: out = in2;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 4 Input Mux
//------------------------------------------------------------------------

module cmn_Mux4 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  input  logic [        1:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      2'd0: out = in0;
      2'd1: out = in1;
      2'd2: out = in2;
      2'd3: out = in3;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 5 Input Mux
//------------------------------------------------------------------------

module cmn_Mux5 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 6 Input Mux
//------------------------------------------------------------------------

module cmn_Mux6 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 7 Input Mux
//------------------------------------------------------------------------

module cmn_Mux7 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  in6,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      3'd6: out = in6;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 8 Input Mux
//------------------------------------------------------------------------

module cmn_Mux8 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  in6,
  in7,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      3'd6: out = in6;
      3'd7: out = in7;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// N Input Mux
//------------------------------------------------------------------------

module cmn_MuxN
#(
  parameter nbits = 1,
  parameter ninputs = 2
)(
  input  logic               [nbits-1:0]   in   [0:ninputs-1], 
  input  logic     [$clog2(ninputs)-1:0]   sel,
  output logic               [nbits-1:0]   out
);

  assign out = in[sel];

endmodule

 /* CMN_MUXES_V */

//========================================================================
// Verilog Components: Registers
//========================================================================

// Note that we place the register output earlier in the port list since
// this is one place we might actually want to use positional port
// binding like this:
//
//  logic [p_nbits-1:0] result_B;
//  cmn_Reg#(p_nbits) result_AB( clk, result_B, result_A );




//========================================================================
// vc-Assert
//========================================================================




//------------------------------------------------------------------------
// CMN_PROPAGATE_X
//------------------------------------------------------------------------






//------------------------------------------------------------------------
// CMN_ASSERT
//------------------------------------------------------------------------










//------------------------------------------------------------------------
// CMN_ASSERT_FAIL
//------------------------------------------------------------------------







//------------------------------------------------------------------------
// CMN_ASSERT_NOT_X
//------------------------------------------------------------------------










  /* CMN_ASSERT_V */


//------------------------------------------------------------------------
// Postive-edge triggered flip-flop
//------------------------------------------------------------------------

module cmn_Reg #(
  parameter p_nbits = 1
) (
  input  logic               clk,  // Clock input
  output logic [p_nbits-1:0] q,    // Data output
  input  logic [p_nbits-1:0] d     // Data input
);

  always_ff @(posedge clk) q <= d;

endmodule

//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with reset
//------------------------------------------------------------------------

module cmn_ResetReg #(
  parameter p_nbits       = 1,
  parameter p_reset_value = 0
) (
  input  logic               clk,    // Clock input
  input  logic               reset,  // Sync reset input
  output logic [p_nbits-1:0] q,      // Data output
  input  logic [p_nbits-1:0] d       // Data input
);

  always_ff @(posedge clk) q <= reset ? p_reset_value : d;

endmodule

//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with enable
//------------------------------------------------------------------------

module cmn_EnReg #(
  parameter p_nbits = 1
) (
  input  logic               clk,  // Clock input
  output logic [p_nbits-1:0] q,    // Data output
  input  logic [p_nbits-1:0] d,    // Data input
  input  logic               en    // Enable input
);

  always_ff @(posedge clk) if (en) q <= d;

endmodule

//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with enable and reset
//------------------------------------------------------------------------

module cmn_EnResetReg #(
  parameter p_nbits       = 1,
  parameter p_reset_value = 0
) (
  input  logic               clk,    // Clock input
  input  logic               reset,  // Sync reset input
  output logic [p_nbits-1:0] q,      // Data output
  input  logic [p_nbits-1:0] d,      // Data input
  input  logic               en      // Enable input
);

  always_ff @(posedge clk) if (reset || en) q <= reset ? p_nbits'(p_reset_value) : d;

endmodule

  /* CMN_REGS_V */


module fixed_point_iterative_Multiplier #(
  parameter int n = 32,  // bit width
  parameter int d = 16,  // number of decimal bits
  parameter bit sign = 1  // 1 if signed, 0 otherwise.
) (
  input logic clk,
  input logic reset,

  output logic recv_rdy,
  input logic recv_val,
  input logic [n - 1:0] a,
  input logic [n - 1:0] b,

  input logic send_rdy,
  output logic send_val,
  output logic [n - 1:0] c
);
  // performs the operation c = a*b
  // Equivalent to taking the integer representations of both numbers,
  // multiplying, and then shifting right
  logic do_carry, do_add, in_wait;

  FXPIterMultControl #(n, d) control (
    .clk(clk),
    .reset(reset),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .send_val(send_val),
    .send_rdy(send_rdy),
    .in_wait(in_wait),
    .do_add(do_add),
    .do_carry(do_carry)
  );

  FXPIterMultDatapath #(n, d) datapath (
    .clk(clk),
    .reset(reset),
    .in_wait(in_wait),
    .do_add(do_add),
    .do_carry((sign != 0) & do_carry),
    .a({{d{(sign != 0) & a[n-1]}}, a}),
    .b(b),
    .c(c)
  );

endmodule

module FXPIterMultControl #(
  parameter int n = 32,
  parameter int d = 16
) (
  input  logic clk,
  input  logic reset,
  input  logic recv_val,
  output logic recv_rdy,
  output logic send_val,
  input  logic send_rdy,
  output logic in_wait,
  output logic do_add,
  output logic do_carry
);
  logic [1:0] IDLE = 2'd0, CALC = 2'd1, DONE = 2'd2;

  logic [1:0] state, next_state;
  logic [$clog2(n)-1:0] counter;
  logic counter_reset;

  // manage state
  always_comb begin
    case (state)
      IDLE: begin
        if (recv_val) next_state = CALC;
        else next_state = IDLE;
      end
      CALC: begin
        if (counter == ($clog2(n))'(n - 1)) next_state = DONE;
        else next_state = CALC;
      end
      DONE: begin
        if (send_rdy) next_state = IDLE;
        else next_state = DONE;
      end
      default: begin
        next_state = IDLE;
      end
    endcase
  end

  // manage datapath
  always_comb begin
    case (state)
      IDLE: begin
        in_wait = 1;
        do_add = 0;
        do_carry = 0;
        counter_reset = 0;
        recv_rdy = 1;
        send_val = 0;
      end
      CALC: begin
        in_wait = 0;
        do_add = 1;
        do_carry = (counter == ($clog2(n))'(n - 1));
        counter_reset = 0;
        recv_rdy = 0;
        send_val = 0;
      end
      DONE: begin
        in_wait = 0;
        do_add = 0;
        do_carry = 0;
        counter_reset = 1;
        recv_rdy = 0;
        send_val = 1;
      end
      default: begin
      end
    endcase
  end

  // reset logic
  always_ff @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  // counter logic
  always_ff @(posedge clk) begin
    if (reset || counter_reset) begin
      counter <= 0;
    end else if (state == CALC) begin
      counter <= counter + 1;
    end else begin
      counter <= counter;
    end
  end

endmodule

module FXPIterMultDatapath #(
  parameter int n = 32,
  parameter int d = 16
) (
  input logic clk,
  input logic reset,
  input logic in_wait,  // waiting for input
  input logic do_add,
  input logic do_carry,
  input logic [n+d-1:0] a,
  input logic [n-1:0] b,
  output logic [n-1:0] c
);
  // accumulator for the current product
  logic [(n+d)-1:0] acc_in;
  logic [(n+d)-1:0] acc_out;

  cmn_ResetReg #(n + d) acc_reg (
    .clk(clk),
    .reset(in_wait | reset),
    .d(acc_in),
    .q(acc_out)
  );

  // holds the `a` input in a register
  logic [(n+d)-1:0] a_const_out;

  cmn_EnResetReg #(n + d) a_const_reg (
    .clk(clk),
    .reset(reset),
    .en(in_wait),
    .d(a),
    .q(a_const_out)
  );

  // holds the shifting `a` input
  logic [(n+d)-1:0] a_in;
  logic [(n+d)-1:0] a_out;

  cmn_ResetReg #(n + d) a_reg (
    .clk(clk),
    .reset(reset),
    .d(a_in),
    .q(a_out)
  );

  // holds the shifting `b` input
  logic [n-1:0] b_in;
  logic [n-1:0] b_out;

  cmn_ResetReg #(n) b_reg (
    .clk(clk),
    .reset(reset),
    .d(b_in),
    .q(b_out)
  );

  // shifts `a` to the left every cycle during calculation
  cmn_Mux2 #(n + d) a_sel (
    .in0(a_out << 1),
    .in1(a),
    .sel(in_wait),
    .out(a_in)
  );

  // shifts `b` to the right every cycle during calculation
  cmn_Mux2 #(n) b_sel (
    .in0(b_out >> 1),
    .in1(b),
    .sel(in_wait),
    .out(b_in)
  );

  logic [n+d-1:0] add_tmp;

  // stores the extra carry information, which allows us to skip the additional
  // `d` cycles we would usually need.
  logic [2*n-1:0] carry_tmp;

  /* verilator lint_off UNUSED */
  // top n-d bits here will be unused.
  logic [2*n-1:0] carry_tmp2;
  /* verilator lint_on UNUSED */

  // a sign-extended to the right length
  assign carry_tmp  = {{(n - d) {a_const_out[n+d-1]}}, a_const_out};
  // left shift by n, then subtract to get the carry
  // this is equivalent to multiplying `a` by `d+1` ones, which is equivalent to the last
  // `d+1` cycles in the multiplication, because `b` is either one-extended or zero-extended
  // from `n` bits to `n+d` bits. This allows us to do the multiplication in `n` cycles only.
  assign carry_tmp2 = ((carry_tmp << (d + 1)) - carry_tmp) << (n - 1);


  // choose between the carry and the add
  cmn_Mux2 #(n + d) carry_sel (
    .in0(a_out),
    .in1(carry_tmp2[n+d-1:0]),
    .sel(do_carry),
    .out(add_tmp)
  );

  // add to the accumulator
  cmn_Mux2 #(n + d) add_sel (
    .in0(acc_out),
    .in1(acc_out + add_tmp),
    .sel(do_add & b_out[0]),
    .out(acc_in)
  );

  assign c = acc_out[n+d-1:d];
endmodule


