// =================================================================================
// Author: Anjelica Bian
// Date: 04/13/2025
// Documentation:
// Spec: Rads the least significant bits with 0s so that the output message has
//       `p_full_bit_width` number of zeros. The entire process is combinational
// PARAMETERS ----------------------------------------------------------------------
// - p_bit_width: Bitwidth of req_msg
// - p_num_concat: Resulting bitwidth after concatentation
// I/O -----------------------------------------------------------------------------
// - clk: Input clock.
// - reset: Input reset.
// - req_msg: Message to concatonate into resp_msg.
// - req_val: Valid signal for input.
// - req_rdy: Ready signal to indicate module is ready to receive the next input.
// - resp_msg: Response message containing p_num_concat number of input messages
//             concatonated together.
// - resp_val: Valid signal for response.
// - resp_rdy: Ready signal to indicate consumer is ready for response.
// =================================================================================

`ifndef FIFO_PACKAGER_V
`define FIFO_PACKAGER_V

module FifoPackager #(
    parameter p_bit_width = 3,
    parameter p_full_bit_width = 6
) (
    input  logic                       clk,
    input  logic                       reset,

    input  logic [p_bit_width-1:0]     req_msg,
    input  logic                       req_val,
    output logic                       req_rdy,

    output logic [p_full_bit_width-1:0] resp_msg,
    output logic                       resp_val,
    input logic                        resp_rdy
);

  assign resp_msg = {req_msg, (p_full_bit_width - p_bit_width){0}};

endmodule

`endif /*FIFO_PACKAGER_V*/

