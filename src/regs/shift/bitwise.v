
`ifndef REGS_SHIFT_BITWISE
`define REGS_SHIFT_BITWISE
//------------------------------------------------------------------------
// N-bit bitwise shift register
//------------------------------------------------------------------------
/*
This is a shift register storing `nbits` total bits.

One bit of data can be inputted per clock cycle, gated by the `en` input.
The entire register will be shifted to the left by one bit when this happens.

For example, here is a simulation of a 4 bit register:
```
reset held high
  0000
en high, d = 1
  0001
en high, d = 0
  0010
override_en high, override = 1111
  1111
```

The entire register can be overridden by the `override` input when `override_en` is high.
Data cannot be inputted when `override_en` is high.
*/
module regs_shift_Bitwise #(
  parameter p_nbits = 8,
  parameter p_reset_value = 0
) (
  input  logic               clk,          // Clock input
  input  logic               reset,        // Sync reset input
  input  logic               d,            // One bit data input
  input  logic               en,           // Enable input
  input  logic [p_nbits-1:0] override,     // Override data input
  input  logic               override_en,  // Enable override
  output logic [p_nbits-1:0] q             // Data output
);

  always_ff @(posedge clk) begin
    if (reset) begin
      q <= {p_nbits{p_reset_value}};
    end else if (override_en) begin
      q <= override;
    end else if ((~override_en) & en) begin
      q <= {q[p_nbits-2:0], d};
    end
  end
endmodule

`endif
