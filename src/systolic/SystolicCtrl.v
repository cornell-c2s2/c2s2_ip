`ifndef SYSTOLICCTRL_V
`define SYSTOLICCTRL_V

`define LOAD 3'b001
`define MAC  3'b010
`define OUT  3'b100

module SystolicCtrl
#(
  parameter size = 16
)(
  input logic clk,
  input logic rst,

  input logic x_fifo_full  [size],
  input logic x_fifo_empty [size],

  input logic w_fifo_full  [size],
  input logic w_fifo_empty [size]
);

  // Buffer Status

  logic full;
  logic empty;

  always_comb begin
    full  = (x_fifo_full[0] & w_fifo_full[0]);
    empty = (x_fifo_empty[0] & w_fifo_empty[0]);
    for(int i = 1; i < size; i++) begin
      full  = (full & x_fifo_full[i] & w_fifo_full[i]);
      empty = (empty & x_fifo_empty[i] & w_fifo_empty[i]);
    end
  end

  // State Transition

  logic [2:0] state;

  always_ff @(posedge clk) begin
    if(rst)
      state <= `LOAD;
    else begin
      case(state)
        `LOAD   : state <= (full ? `MAC : `LOAD);
        `MAC    : state <= (empty ? `OUT : `MAC);
        `OUT    : state <= `OUT;
        default : state <= `LOAD;
      endcase
    end
  end

  // Output Logic



endmodule

`endif