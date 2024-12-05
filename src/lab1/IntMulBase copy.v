//========================================================================
// Integer Multiplier Fixed-Latency Implementation
//========================================================================

`ifndef LAB1_IMUL_INT_MUL_BASE_V
`define LAB1_IMUL_INT_MUL_BASE_V

`include "vc/trace.v"
`include "vc/regs.v"
`include "vc/muxes.v"
`include "vc/arithmetic.v"


//========================================================================
// Integer Multiplier Fixed-Latency Implementation
//========================================================================

module lab1_imul_IntMulBase
(
  input  logic        clk,
  input  logic        reset,

  input  logic        istream_val,
  output logic        istream_rdy,
  input  logic [63:0] istream_msg,

  output logic        ostream_val,
  input  logic        ostream_rdy,
  output logic [31:0] ostream_msg

);


  // control signals
  logic a_mux_sel;
  logic b_mux_sel;
  logic result_mux_sel;
  logic add_mux_sel;
  logic result_en;

  // data signals
  logic b_lsb;

  lab1_imul_ControlUnit control_unit (
    .*
  );

  lab1_imul_Datapath datapath (
    .*
  );
  //----------------------------------------------------------------------
  // Line Tracing
  //----------------------------------------------------------------------

  `ifndef SYNTHESIS

  logic [`VC_TRACE_NBITS-1:0] str;
  `VC_TRACE_BEGIN
  begin

    $sformat( str, "%x", istream_msg );
    vc_trace.append_val_rdy_str( trace_str, istream_val, istream_rdy, str );

    vc_trace.append_str( trace_str, "(" );

    // $sformat ( str, "%x * %x = %x; state = %x; counter = %d", istream_msg[63:32], istream_msg[31:0], ostream_msg, state_reg, counter );
    // $sformat ( str, "a=%d, b=%d, add=%d, result_reg=%d; state=%x; counter=%d", a_reg_out, b_reg_out, adder_out, ostream_msg, state_reg, counter );
    // $sformat ( str, "a=%d, b_lsb=%b, add=%d, result_mux=%d, result_reg=%d; state=%x; counter=%d", a_reg_out, b_lsb, add_mux_out, result_mux_out, ostream_msg, state_reg, counter );
    vc_trace.append_str( trace_str, str );

    vc_trace.append_str( trace_str, ")" );

    $sformat( str, "%x", ostream_msg );
    vc_trace.append_val_rdy_str( trace_str, ostream_val, ostream_rdy, str );

  end
  `VC_TRACE_END

  `endif /* SYNTHESIS */

endmodule



module lab1_imul_Datapath (
    input logic clk,
    input logic reset,
    input logic b_mux_sel,
    input logic a_mux_sel,
    input logic result_mux_sel,
    input logic add_mux_sel,
    input logic result_en,
    output logic b_lsb,
    input logic [63:0] istream_msg,
    output logic [31:0] ostream_msg
  );

  logic [31:0] b_reg_out;
  logic [31:0] a_reg_out;
  logic [31:0] result_reg_out;
  assign ostream_msg = result_reg_out;

  logic [31:0] right_shift_out;
  logic [31:0] left_shift_out;

  logic [31:0] adder_out;

  logic [31:0] b_mux_out;
  logic [31:0] a_mux_out;
  logic [31:0] result_mux_out;
  logic [31:0] add_mux_out;

  assign b_lsb = b_reg_out[0];


  vc_Mux2#(32) b_mux(
    .in0 (right_shift_out), //output of right shift
    .in1 (istream_msg[31:0]),
    .sel (b_mux_sel),
    .out (b_mux_out)
  );

  vc_Mux2#(32) a_mux(
    .in0 (left_shift_out), //output of left shift 
    .in1 (istream_msg[63:32]),
    .sel (a_mux_sel),
    .out (a_mux_out)
  );

  vc_Mux2#(32) result_mux(
    .in0 (add_mux_out),
    .in1 (0),
    .sel (result_mux_sel),
    .out (result_mux_out)
  );

  vc_Mux2#(32) add_mux(
    .in0 (adder_out),
    .in1 (result_reg_out),
    .sel (add_mux_sel),
    .out (add_mux_out)
  );


  vc_ResetReg#(32) b_reg(
    .clk   (clk),
    .reset (reset),
    .d     (b_mux_out),
    .q     (b_reg_out)
  );



  vc_ResetReg#(32,0) a_reg(
    .clk   (clk),
    .reset (reset),
    .d     (a_mux_out),
    .q     (a_reg_out)
  );

  vc_EnResetReg#(32,0) result_reg(
    .clk   (clk),
    .reset (reset),
    .d     (result_mux_out),
    .q     (result_reg_out),
    .en    (result_en)
  );


  vc_RightLogicalShifter#(32,1) right_shift(
    .in    (b_reg_out),
    .shamt (1),
    .out   (right_shift_out)
  );

  vc_LeftLogicalShifter#(32,1) left_shift(
    .in    (a_reg_out),
    .shamt (1),
    .out   (left_shift_out)
  );


  vc_SimpleAdder#(32) adder( //not sure if we need to create our own carry in/carry out and use regular adder 
    .in0 (a_reg_out),
    .in1 (result_reg_out),
    .out (adder_out)
  );

endmodule

module lab1_imul_ControlUnit 
(
  input  logic clk,
  input  logic reset,

  // dataflow signals
  input  logic istream_val,
  input  logic ostream_rdy,
  output logic istream_rdy,
  output logic ostream_val,

  // control signals
  input  logic b_lsb,        
  output logic a_mux_sel,
  output logic b_mux_sel,
  output logic result_mux_sel,
  output logic add_mux_sel,
  output logic result_en
);
  //----------------------------------------------------------------------
  // State Definitions
  //----------------------------------------------------------------------
  localparam STATE_IDLE = 2'h0;
  localparam STATE_CALC = 2'h1;
  localparam STATE_DONE = 2'h2;

  //----------------------------------------------------------------------
  // State
  //----------------------------------------------------------------------
  logic [1:0] state_reg;
  logic [1:0] state_next;
  logic [5:0] counter;

  always_ff @( posedge clk ) begin 
    if ( reset ) begin
      state_reg <= STATE_IDLE;
    end
    else begin
      if ( state_next == STATE_CALC ) begin
        if ( state_reg == STATE_IDLE ) begin
          counter <= 0;
        end
        else begin 
          counter <= counter + 1;
        end
      end
      state_reg <= state_next;
    end
  end

  //----------------------------------------------------------------------
  // State Transitions
  //----------------------------------------------------------------------

  logic req_go;
  logic resp_go;
  logic is_calc_done;

  assign req_go = istream_val && istream_rdy;
  assign resp_go = ostream_val && ostream_rdy;
  assign is_calc_done = (counter == 32);

  always_comb begin

    state_next = state_reg;

    case ( state_reg )
      STATE_IDLE: if ( req_go       ) state_next = STATE_CALC;
      STATE_CALC: if ( is_calc_done ) state_next = STATE_DONE;
      STATE_DONE: if ( resp_go      ) state_next = STATE_IDLE;
      default:    state_next = 'x;
    endcase

  end

  //----------------------------------------------------------------------
  // State Outputs
  //----------------------------------------------------------------------
  function void cs
  (
    input logic       cs_istream_rdy,
    input logic       cs_ostream_val,
    input logic       cs_a_mux_sel,
    input logic       cs_b_mux_sel,
    input logic       cs_result_mux_sel,
    input logic       cs_add_mux_sel,
    input logic       cs_result_en
  );
  begin
    istream_rdy    = cs_istream_rdy;
    ostream_val    = cs_ostream_val;
    a_mux_sel      = cs_a_mux_sel;
    b_mux_sel      = cs_b_mux_sel;
    result_mux_sel = cs_result_mux_sel;
    add_mux_sel    = cs_add_mux_sel;
    result_en      = cs_result_en;
  end
  endfunction

  // Labels for Mealy transistions

  logic do_add;
  assign do_add = b_lsb;

  // Set outputs using a control signal "table"

  always_comb begin
    case ( state_reg )
      //                             istream   ostream  a_mux    b_mux    result   add_mux   result
      //                             rdy       val      sel      sel      mux_sel  sel       en
      STATE_IDLE:                cs( 1,        0,       1,       1,       1,       1,        1);
      STATE_CALC: if ( do_add )  cs( 0,        0,       0,       0,       0,       0,        1);
                  else           cs( 0,        0,       0,       0,       0,       1,        1);
      STATE_DONE:                cs( 0,        1,       1,       1,       0,       1,        0);
      default                    cs('x,       'x,      'x,      'x,      'x,      'x,       'x);
    endcase

  end


endmodule

`endif /* LAB1_IMUL_INT_MUL_BASE_V */

