`ifndef FIFO_V
`define FIFO_V

module FIFO
#(
  parameter size  = 3
  parameter nbits = 16
)(
  input  logic             clk,
  input  logic             rst,
  input  logic             wen,
  input  logic             ren,
  //input  logic [nbits-1:0] d_in,
  output logic             full,
  output logic             empty,
  //output logic [nbits-1:0] q_out
);

  // Status Signals

  logic _full;
  logic _empty;
  logic [$clog2(size)-1:0] count;

  always_ff @(posedge clk) begin
    if(rst) begin
      count  <= 0;
      _full  <= 0;
      _empty <= 0;
    end
    else begin
      case(wen)
        // read only
        1'b0: begin
          count  <= (count - ren);
          _full  <= 0;
          _empty <= ((count - ren) == 0);
        end
        // write only
        1'b1: begin
          count <= count + !ren;
          _full <= ((count + !ren) == size);
          _empty <= 0;
        end
      endcase
    end
  end

  assign full  = _full;
  assign empty = _empty;

endmodule

`endif