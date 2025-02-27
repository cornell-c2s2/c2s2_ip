// =================================================================================
// Author: Johnny Martinez
// Date: 02/16/2025
// Documentation:
// Spec: Receives p_num_concat valid inputs and merges them into one output. First 
// message composes LSBs.
// Example:
// Cycle 1: send in 001
// Cycle 2: send in 010
// Cycle 3: output 010001
// PARAMETERS ----------------------------------------------------------------------
// - p_bit_width: Bitwidth of req_msg
// - p_num_concat: Number of req_msgs (i.e. inputs) to concatanate
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
    parameter p_num_concat = 2
) (
    input  logic                       clk,
    input  logic                       reset,

    input  logic [p_bit_width-1:0]     req_msg,
    input  logic                       req_val,
    output logic                       req_rdy,

    output logic [(p_bit_width*2)-1:0] resp_msg,
    output logic                       resp_val,
    input logic                        resp_rdy
);

//============================LOCAL_PARAMETERS=================================
  // - out: register that holds concatanated output of the req_msgs
  // - counter: counter the number of valid req_msgs received
  logic [p_bit_width-1:0]          out [p_num_concat];
  logic [$clog2(p_num_concat):0]   counter;

//================================DATAPATH=====================================
  always_comb begin
    for (int i = 0; i < p_num_concat; i = i + 1) begin
        resp_msg[i*p_bit_width +: p_bit_width] = out[i];
    end
  end
  assign resp_val = counter >= p_num_concat;
  assign req_rdy  = counter < p_num_concat;

//===============================CTRL_LOGIC====================================
always_ff @(posedge clk) begin
    if(reset) begin
      for (int i = 0; i < p_num_concat; i = i + 1) begin
        out[i] <= '0;
      end
      counter <= '0;
    end
    else begin
        if(req_val && (counter < p_num_concat)) begin
            out[counter] <= req_msg;
            counter      <= counter + 1;
        end
        if(counter >= p_num_concat && resp_rdy) begin
            counter <= 0;
        end
    end
  end


endmodule

`endif /*FIFO_PACKAGER_V*/

