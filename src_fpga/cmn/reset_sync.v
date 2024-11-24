//======================================================================
// Reset Synchronizer
//======================================================================
// This module serves as the reset synchronizer for FPGA emulation to 
// conduct physical tests.

`include "cmn/regs.v"

`ifndef CMN_RESET_SYNC_V
`define CMN_RESET_SYNC_V

module reset_synchronizer (
  input  logic clk,
  input  logic reset,
  output logic s_reset
);

  // Instantiate wires for between registers
  logic out_reset_reg0,
        out_reset_reg1;

  // Instantiate registers to delay reset signal
  cmn_Reg reg0 (
    .clk (clk),
    .q   (out_reset_reg0),
    .d   (reset)
  );

  cmn_Reg reg1 (
    .clk (clk),
    .q   (out_reset_reg1),
    .d   (out_reset_reg0)
  );

  // OR reset signal with delayed reset signal
  assign s_reset = out_reset_reg1 | reset;
  
endmodule

`endif /* CMN_RESET_SYNC_V */