//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with reset
//------------------------------------------------------------------------

module arr_ResetReg #(
  parameter BIT_WIDTH   = 1,
  parameter RESET_VALUE = 0,
  parameter N_ELEMENTS  = 1
) (
  input  logic                 clk,                    // Clock input
  input  logic                 reset,                  // Sync reset input
  output logic [BIT_WIDTH-1:0] q    [N_ELEMENTS-1:0],  // Data output
  input  logic [BIT_WIDTH-1:0] d    [N_ELEMENTS-1:0]   // Data input
);

  always_ff @(posedge clk) q <= reset ? RESET_VALUE : d;

endmodule

//------------------------------------------------------------------------
// Postive-edge triggered flip-flop with enable and reset
//------------------------------------------------------------------------

module arr_EnResetReg #(
  parameter BIT_WIDTH   = 1,
  parameter RESET_VALUE = 0,
  parameter N_ELEMENTS  = 1
) (
  input  logic                 clk,                    // Clock input
  input  logic                 reset,                  // Sync reset input
  output logic [BIT_WIDTH-1:0] q    [N_ELEMENTS-1:0],  // Data output
  input  logic [BIT_WIDTH-1:0] d    [N_ELEMENTS-1:0],  // Data input
  input  logic                 en                      // Enable input
);

  always_ff @(posedge clk) if (reset || en) q <= reset ? RESET_VALUE : d;

endmodule

