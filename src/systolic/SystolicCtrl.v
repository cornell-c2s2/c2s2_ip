`ifndef SYSTOLICCTRL_V
`define SYSTOLICCTRL_V

`define LOAD 3'b001
`define MAC  3'b010
`define OUT  3'b100

module SystolicCtrl
#(
  parameter SIZE = 4
)(
  input  logic clk,
  input  logic rst,
  
  output logic mac_en,

  input  logic x_recv_val,
  output logic x_recv_rdy,

  input  logic w_recv_val,
  output logic w_recv_rdy,

  input  logic x_fifo_full  [SIZE],
  input  logic x_fifo_empty [SIZE],
  output logic x_fifo_wen   [SIZE],
  output logic x_fifo_ren   [SIZE],

  input  logic w_fifo_full  [SIZE],
  input  logic w_fifo_empty [SIZE],
  output logic w_fifo_wen   [SIZE],
  output logic w_fifo_ren   [SIZE],
  
  output logic mac_rdy,
  output logic out_rdy
);

  // Buffer Status

  logic full;
  logic empty;

  logic x_full;
  logic w_full;

  always_comb begin
    x_full = 1;
    w_full = 1;
    for(int i = 0; i < SIZE; i++) begin
      x_full = (x_full & x_fifo_full[i]);
      w_full = (w_full & w_fifo_full[i]);
    end
  end

  assign full = (x_full & w_full);

  always_comb begin
    empty = 1;
    for(int i = 0; i < SIZE; i++)
      empty = (empty & x_fifo_empty[i] & w_fifo_empty[i]);
  end

  // State Transition

  logic [2:0]              state;
  logic [$clog2(SIZE)-1:0] out_lat_count;
  logic                    out_hit;

  always_ff @(posedge clk) begin
    if(rst)
      out_lat_count <= 0;
    else begin
      case(state)
        `LOAD : out_lat_count <= 0;
        `MAC  : out_lat_count <= (out_lat_count + {{(SIZE-1){1'b0}}, empty});
        `OUT  : out_lat_count <= out_lat_count;
        default : out_lat_count <= 0;
      endcase
    end
  end

  assign out_hit = (out_lat_count == $clog2(SIZE)'(SIZE-1));

  always_ff @(posedge clk) begin
    if(rst)
      state <= `LOAD;
    else begin
      case(state)
        `LOAD   : state <= (full ? `MAC : `LOAD);
        `MAC    : state <= (out_hit ? `OUT : `MAC);
        `OUT    : state <= `OUT;
        default : state <= `LOAD;
      endcase
    end
  end

  // Output Logic

  always_comb begin
    for(int i = 0; i < SIZE; i++) begin
      x_fifo_wen[i] = ((state == `LOAD) & ~x_full & x_recv_val);
      w_fifo_wen[i] = ((state == `LOAD) & ~w_full & w_recv_val);
    end
    x_recv_rdy = ((state == `LOAD) & ~x_full);
    w_recv_rdy = ((state == `LOAD) & ~w_full);
  end

  assign mac_en = ((state == `MAC) | (state == `OUT));
  
  always_ff @(posedge clk) begin
    x_fifo_ren[0] <= (rst ? 0 : (((state == `LOAD) & full) | ((state == `MAC) & ~empty)));
    w_fifo_ren[0] <= (rst ? 0 : (((state == `LOAD) & full) | ((state == `MAC) & ~empty)));
    for(int i = 1; i < SIZE; i++) begin
      x_fifo_ren[i] <= (rst ? 0 : ((state == `MAC) & ~empty & x_fifo_ren[i-1]));
      w_fifo_ren[i] <= (rst ? 0 : ((state == `MAC) & ~empty & w_fifo_ren[i-1]));
    end
  end

  assign mac_rdy = (state == `MAC);
  assign out_rdy = (state == `OUT);

endmodule

`endif