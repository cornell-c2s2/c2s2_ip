module crossbar_controller (
  indata,
  w,
  s,
  defaultout
);
  input [5:0] in;
  input w;
  input s;

  output [5:0] defaultout;
  reg defaultout;

  /*
    Outputs 6b control bus of 2 1-hot 3b strings, 1 for input and 1 for output.
    For each 3b wire:
    default, both pins low --> 100
    SPI pin high --> 010
    GDS pin high --> 001
     */

  always @(indata, w, s) begin
    if (w == 1'b1) defaultout <= 6'b001001;
    else if (s == 1'b1) defaultout <= 6'b010010;
    else defaultout <= indata;
  end

endmodule
