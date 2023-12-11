`ifndef FXP_SQRT
`define FXP_SQRT

`include "src/cmn/muxes.v"
`include "src/cmn/regs.v"

// fxp_sqrt in Verilog

module Fxp_sqrt #(
  parameter int BIT_WIDTH = 32,
  parameter int F_BITS = 16
) (
  input logic reset,
  input logic clk,

  input  logic [BIT_WIDTH - 1:0] recv_msg,
  input  logic                   recv_val,
  output logic                   recv_rdy,

  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic                   send_val,
  input  logic                   send_rdy
);

  logic res_mux_sel;
  logic q_state_mux_sel;
  logic ac_mux_sel;
  logic x_mux_sel;
  logic send_mux_sel;

  logic msb_gtz;

  // Datapath Unit
  datapath_module #(
    .BIT_WIDTH(BIT_WIDTH),
    .F_BITS(F_BITS)
  ) dpath (
    .*
  );

  // Control Unit
  control_module #(
    .BIT_WIDTH(BIT_WIDTH),
    .F_BITS(F_BITS)
  ) ctrl (
    .*
  );

endmodule

//========================================================================
// Datapath Module
//========================================================================
module datapath_module #(
  parameter int BIT_WIDTH = 32,
  parameter int F_BITS = 16
) (
  input logic clk,

  input logic [BIT_WIDTH-1:0] recv_msg,

  input logic res_mux_sel,
  input logic q_state_mux_sel,
  input logic ac_mux_sel,
  input logic x_mux_sel,
  input logic send_mux_sel,

  output logic msb_gtz,

  output logic [BIT_WIDTH-1:0] send_msg
);

  logic [BIT_WIDTH-1:0] x;
  logic [BIT_WIDTH-1:0] x_next;  // radicand copy
  logic [BIT_WIDTH-1:0] q;
  logic [BIT_WIDTH-1:0] q_next;  // intermediate root (quotient)
  logic [BIT_WIDTH+1:0] ac;
  logic [BIT_WIDTH+1:0] ac_next;  // accumulator (2 bits wider)
  logic [BIT_WIDTH+1:0] test_res;  // sign test result (2 bits wider)

  cmn_Mux2 #(
    .p_nbits(BIT_WIDTH + BIT_WIDTH + 2)
  ) ac_x_mux (
    .in0({test_res[BIT_WIDTH-1:0], x, 2'b0}),
    .in1({ac[BIT_WIDTH-1:0], x, 2'b0}),
    .sel(res_mux_sel),
    .out({ac_next, x_next})
  );

  cmn_Mux2 #(
    .p_nbits(BIT_WIDTH)
  ) q_mux (
    .in0({q[BIT_WIDTH-2:0], 1'b1}),
    .in1((q << 1)),
    .sel(res_mux_sel),
    .out(q_next)
  );

  assign test_res = ac - {q, 2'b01};

  logic [BIT_WIDTH-1:0] q_out;

  // q state mux
  cmn_Mux2 #(
    .p_nbits(BIT_WIDTH)
  ) q_state_mux (
    .in0(0),
    .in1(q_next),
    .sel(q_state_mux_sel),
    .out(q_out)
  );

  // q reg
  cmn_Reg #(
    .p_nbits(BIT_WIDTH)
  ) q_reg (
    .clk(clk),
    .d  (q_out),
    .q  (q)
  );

  logic [2*BIT_WIDTH+1:0] acx;
  assign acx = {{BIT_WIDTH{1'b0}}, recv_msg, 2'b0};

  logic [BIT_WIDTH+1:0] ac_mux_out;

  // ac mux
  cmn_Mux2 #(
    .p_nbits(BIT_WIDTH + 2)
  ) ac_mux (
    .in0(acx[2*BIT_WIDTH+1:BIT_WIDTH]),
    .in1(ac_next),
    .sel(ac_mux_sel),
    .out(ac_mux_out)
  );

  // ac reg
  cmn_Reg #(
    .p_nbits(BIT_WIDTH + 2)
  ) ac_reg (
    .clk(clk),
    .d  (ac_mux_out),
    .q  (ac)
  );

  logic [BIT_WIDTH-1:0] x_mux_out;

  // x mux
  cmn_Mux2 #(
    .p_nbits(BIT_WIDTH)
  ) x_mux (
    .in0(acx[BIT_WIDTH-1:0]),
    .in1(x_next),
    .sel(x_mux_sel),
    .out(x_mux_out)
  );

  // x reg
  cmn_Reg #(
    .p_nbits(BIT_WIDTH)
  ) x_reg (
    .clk(clk),
    .d  (x_mux_out),
    .q  (x)
  );

  // send mux
  cmn_Mux2 #(
    .p_nbits(BIT_WIDTH)
  ) send_mux (
    .in0(0),
    .in1(q),
    .sel(send_mux_sel),
    .out(send_msg)
  );

  assign msb_gtz = test_res[BIT_WIDTH+1] == 0;

endmodule

//========================================================================
// Control Module
//========================================================================
module control_module #(
  parameter int BIT_WIDTH = 32,
  parameter int F_BITS = 16
) (
  input logic clk,
  input logic reset,

  input  logic recv_val,
  output logic recv_rdy,
  output logic send_val,
  input  logic send_rdy,

  input logic msb_gtz,

  output logic res_mux_sel,
  output logic q_state_mux_sel,
  output logic ac_mux_sel,
  output logic x_mux_sel,
  output logic send_mux_sel
);

  localparam int ITER = (BIT_WIDTH + F_BITS) >> 1;  // iterations are half radicand width
  logic [$clog2(ITER):0] i;     // iteration counter

  logic [1:0] currentState;
  logic [1:0] nextState;

  logic [1:0] IDLE = 2'd0, CALC = 2'd1, DONE = 2'd3;

  // Next State Comb Logic
  always_comb begin
    case (currentState)
      IDLE:    if (recv_val && recv_rdy) nextState = CALC;
               else nextState = IDLE;
      CALC:    if (i == ITER[$clog2(ITER):0] - 1) nextState = DONE;
               else nextState = CALC;
      DONE:    if (send_rdy && send_val) nextState = IDLE;
               else nextState = DONE;
      default: nextState = IDLE;
    endcase
  end

  // Output Comb Logic
  always_comb begin
    case (currentState)
      IDLE: begin
        recv_rdy = 1;
        res_mux_sel = 'x;
        q_state_mux_sel = 0;
        ac_mux_sel = 0;
        x_mux_sel = 0;
        send_mux_sel = 0;
        send_val = 0;
      end
      CALC:
      if (msb_gtz) begin
        recv_rdy = 0;
        res_mux_sel = 0;
        q_state_mux_sel = 1;
        ac_mux_sel = 1;
        x_mux_sel = 1;
        send_mux_sel = 0;
        send_val = 0;
      end else begin
        recv_rdy = 0;
        res_mux_sel = 1;
        q_state_mux_sel = 1;
        ac_mux_sel = 1;
        x_mux_sel = 1;
        send_mux_sel = 0;
        send_val = 0;
      end
      DONE: begin
        recv_rdy = 0;
        res_mux_sel = 'x;
        q_state_mux_sel = 'x;
        ac_mux_sel = 'x;
        x_mux_sel = 'x;
        send_mux_sel = 1;
        send_val = 1;
      end
      default: begin
        recv_rdy = 'x;
        res_mux_sel = 'x;
        q_state_mux_sel = 'x;
        ac_mux_sel = 'x;
        x_mux_sel = 'x;
        send_mux_sel = 'x;
        send_val = 'x;
      end
    endcase
  end

  // State FFs
  always_ff @(posedge clk) begin
    if (reset) begin
      currentState <= IDLE;
    end else begin
      currentState <= nextState;
    end
  end

  // Counter logic
  always_ff @(posedge clk) begin
    case (currentState)
      IDLE: i <= 0;
      CALC: i <= i + 1;
      default: i <= i;
    endcase
  end

endmodule

`endif
