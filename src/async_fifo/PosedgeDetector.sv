// =================================================================================
// Author: Johnny Martinez
// Date:
// Documentation:
// Spec:
// PARAMETERS ----------------------------------------------------------------------
// I/O -----------------------------------------------------------------------------
// =================================================================================

`ifndef POSEDGE_DETECTOR_V
`define POSEDGE_DETECTOR_V

module PosedgeDetector (
    input  logic                       clk,
    input  logic                       reset,

    input  logic                       req_val,
    output logic                       resp_val
);

//============================LOCAL_PARAMETERS=================================
logic               prev_req_val;

//================================DATAPATH=====================================
// When req_val is high, ONE THE SAME CYCLE resp_val set high. Therefore,
// registers should NOT be used on req_msg and resp_rdy...
assign resp_val = ~prev_req_val & req_val;

//===============================CTRL_LOGIC====================================
always_ff @(posedge clk) begin
    if(reset) begin
        prev_req_val   <= '0;
    end
    else begin
        prev_req_val   <= req_val;
    end
  end

endmodule

`endif /*POSEDGE_DETECTOR_V*/

