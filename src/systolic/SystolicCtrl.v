`ifndef SYSTOLICCTRL_V
`define SYSTOLICCTRL_V

`define LOAD 3'b001
`define MAC  3'b010
`define OUT  3'b100

module SystolicCtrl
#(
  parameter size = 4
)(
  input  logic clk,
  input  logic rst,
  
  output logic mac_en,

  input  logic x_recv_val,
  output logic x_recv_rdy,

  input  logic w_recv_val,
  output logic w_recv_rdy,

  input  logic x_fifo_full  [size],
  input  logic x_fifo_empty [size],
  output logic x_fifo_wen   [size],
  output logic x_fifo_ren   [size],

  input  logic w_fifo_full  [size],
  input  logic w_fifo_empty [size],
  output logic w_fifo_wen   [size],
  output logic w_fifo_ren   [size]
);

  // Buffer Status

  logic full;
  logic empty;

  logic x_full;
  logic w_full;

  always_comb begin
    x_full = 1;
    w_full = 1;
    for(int i = 0; i < size; i++) begin
      x_full = (x_full & x_fifo_full[i]);
      w_full = (w_full & w_fifo_full[i]);
    end
  end

  assign full = (x_full & w_full);

  always_comb begin
    empty = 1;
    for(int i = 0; i < size; i++)
      empty = (empty & x_fifo_empty[i] & w_fifo_empty[i]);
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

  always_comb begin
    for(int i = 0; i < size; i++) begin
      x_fifo_wen[i] = ((state == `LOAD) & ~x_full & x_recv_val);
      w_fifo_wen[i] = ((state == `LOAD) & ~w_full & x_recv_val);
    end
    x_recv_rdy = ((state == `LOAD) & ~x_full);
    w_recv_rdy = ((state == `LOAD) & ~w_full);
  end

  assign mac_en = ((state == `MAC) | (state == `OUT));
  
  always_ff @(posedge clk) begin
    x_fifo_ren[0] <= (rst ? 0 : (((state == `LOAD) & full) | ((state == `MAC) & ~empty)));
    w_fifo_ren[0] <= (rst ? 0 : (((state == `LOAD) & full) | ((state == `MAC) & ~empty)));
    for(int i = 1; i < size; i++) begin
      x_fifo_ren[i] <= (rst ? 0 : ((state == `MAC) & ~empty & x_fifo_ren[i-1]));
      w_fifo_ren[i] <= (rst ? 0 : ((state == `MAC) & ~empty & w_fifo_ren[i-1]));
    end
  end

endmodule

`endif