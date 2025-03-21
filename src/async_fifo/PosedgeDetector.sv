// =================================================================================
// Author: Johnny Martinez
// Date:
// Documentation:
// Spec: On a rising edge of ext_req_val, forward ext_req_msg to ext_resp_msg and
// set ext_resp_val high for one clock cycle! TODO: Update spec...
// PARAMETERS ----------------------------------------------------------------------
// - p_bit_width: Bitwidth of req_msg

// I/O -----------------------------------------------------------------------------


// =================================================================================

`ifndef POSEDGE_DETECTOR_V
`define POSEDGE_DETECTOR_V

module PosedgeDetector (
    input  logic                       clk,
    input  logic                       reset,

    // input  logic [p_bit_width-1:0]     req_msg,
    input  logic                       req_val,
    // output logic                       req_rdy,

    // output logic [p_bit_width-1:0]     resp_msg,
    output logic                       resp_val
    // input logic                        resp_rdy
);

//============================LOCAL_PARAMETERS=================================
logic               prev_req_val;
// logic               prev_resp_rdy;
// logic [p_bit_width] prev_req_msg;

//================================DATAPATH=====================================
// When req_val is high, ONE THE SAME CYCLE resp_val set high. Therefore,
// registers should NOT be used on req_msg and resp_rdy...
assign resp_val = ~prev_req_val & req_val;
// assign resp_msg = prev_req_msg;
// assign req_rdy  = prev_resp_rdy;
// assign resp_msg = req_msg;
// assign req_rdy  = resp_rdy;

//===============================CTRL_LOGIC====================================
always_ff @(posedge clk) begin
    if(reset) begin
        prev_req_val   <= '0;
        // prev_resp_rdy  <= '0;
        // prev_req_msg   <= '0;
    end
    else begin
        prev_req_val   <= req_val;
        // prev_resp_rdy  <= resp_rdy;
        // prev_req_msg   <= req_msg;
    end
  end

endmodule

`endif /*POSEDGE_DETECTOR_V*/

