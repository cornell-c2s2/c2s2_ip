`ifndef SYSTOLICCTRL_V
`define SYSTOLICCTRL_V

module SystolicCtrl
#(
  parameter size = 16
)(
  input  logic                    clk,
  input  logic                    rst,
  input  logic                    mac_en,
  
  output logic [$clog2(size)-1:0] x_fifo_sel,
  output logic                    x_fifo_wen   [size],
  output logic                    x_fifo_ren   [size],
  input  logic                    x_fifo_full  [size],
  input  logic                    x_fifo_empty [size],

  output logic [$clog2(size)-1:0] w_fifo_sel,
  output logic                    w_fifo_wen   [size],
  output logic                    w_fifo_ren   [size],
  input  logic                    w_fifo_full  [size],
  input  logic                    w_fifo_empty [size]
);

  // Buffer Status

  logic buf_full;
  logic buf_empty;

  always_comb begin
    buf_full  = (x_fifo_full[0] & w_fifo_full[0]);
    buf_empty = (x_fifo_empty[0] & w_fifo_empty[0]);
    for(int i = 1; i < size; i++) begin
      buf_full  = (buf_full & x_fifo_full[i] & w_fifo_full[i]);
      buf_empty = (buf_empty & x_fifo_empty[i] & w_fifo_empty[i]);
    end
  end

  // State Transition

  localparam STATE_LOAD = 2'b00;
  localparam STATE_MAC  = 2'b01;
  localparam STATE_OUT  = 2'b10;

  logic [1:0] state;

  always_ff @(posedge clk) begin
    case(state)
      STATE_LOAD : state <= (buf_full ? STATE_MAC : STATE_LOAD);
      STATE_MAC  : state <= (buf_empty ? STATE_OUT : STATE_MAC);
      STATE_OUT  : state <= STATE_OUT;
    endcase
  end

  // Output Logic



endmodule

`endif