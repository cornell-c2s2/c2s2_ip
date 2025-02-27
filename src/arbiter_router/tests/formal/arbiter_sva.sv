`include "arbiter_router/arbiter.v"

module arbiter_sva #(
  parameter int nbits   = 32,
  parameter int ninputs = 3,
  localparam int addr_nbits = $clog2(ninputs)
)(
  input  logic clk,
  input  logic reset,

  // Input (receive) interface for each source.
  input logic             istream_val [ninputs],
  input logic             istream_rdy [ninputs],
  input logic [nbits-1:0] istream_msg [ninputs],

  // Output (send) interface.
  input logic                        ostream_val,
  input logic                        ostream_rdy,
  input logic [addr_nbits+nbits-1:0] ostream_msg
);
  logic [addr_nbits-1:0] grants_index;  // which input is granted access to send to SPI
  logic [addr_nbits-1:0] old_grants_index;
  logic [addr_nbits-1:0] encoder_out;
  logic [     nbits-1:0] ostream_msg_data;
  logic [addr_nbits-1:0] ostream_msg_addr;

  assign grants_index [addr_nbits-1:0] = arbiter_router_Arbiter.grants_index;
  assign old_grants_index [addr_nbits-1:0] = arbiter_router_Arbiter.old_grants_index;
  assign encoder_out [addr_nbits-1:0] = arbiter_router_Arbiter.encoder_out;
  assign ostream_msg_data [nbits-1:0] = arbiter_router_Arbiter.ostream_msg_data;
  assign ostream_msg_addr [addr_nbits-1:0] = arbiter_router_Arbiter.ostream_msg_addr;

  //-------------------------------------------------------------------------
  // Hold Behavior
  // If the previously granted input (old_grants_index) is still valid,
  // then the current grant must remain the same.
  //-------------------------------------------------------------------------
  property p_hold_previous;
    @(posedge clk) disable iff (reset)
      (istream_val[old_grants_index] == 1'b1)
        |-> (grants_index === old_grants_index);
  endproperty

  hold_previous : assert property (p_hold_previous);

  //-------------------------------------------------------------------------
  // Grant Behavior
  // If the previously granted input (old_grants_index) is not valid, then
  // the next grant should be assigned to the highest priority input (the LSB)
  //-------------------------------------------------------------------------

  property p_select_new_lsb;
    @(posedge clk) disable iff (reset)
      (!istream_val[old_grants_index] && (istream_val[0] || istream_val[1] || istream_val[2])) |-> 
        ( (grants_index == 0 && istream_val[0]) ||
          (grants_index == 1 && !istream_val[0] && istream_val[1]) ||
          (grants_index == 2 && !istream_val[0] && !istream_val[1] && istream_val[2]) );
  endproperty

  select_new_lsb : assert property (p_select_new_lsb);

  //-------------------------------------------------------------------------
  // Output Behavior
  // The output message should be the same as the input message of the granted input
  //-------------------------------------------------------------------------

  property p_output_message;
    @(posedge clk) disable iff (reset)
      ostream_val |-> ((ostream_msg[nbits-1:0] === istream_msg[grants_index]) &&
                      (ostream_msg[nbits+addr_nbits-1:nbits] === grants_index));
  endproperty

  output_message : assert property (p_output_message);

  //-------------------------------------------------------------------------
  // Output Ready Behavior
  // The output ready signal should be the same as the granted input ready signal
  //-------------------------------------------------------------------------
  property p_istream_ready;
    @(posedge clk) disable iff (reset)
      ( (istream_rdy[0] === ((grants_index == 0) ? ostream_rdy : 1'b0)) &&
        (istream_rdy[1] === ((grants_index == 1) ? ostream_rdy : 1'b0)) &&
        (istream_rdy[2] === ((grants_index == 2) ? ostream_rdy : 1'b0)) );
  endproperty

  istream_ready : assert property (p_istream_ready);

  //-------------------------------------------------------------------------
  // Output Valid Behavior
  // The output valid signal should be the same as the granted input valid signal
  //-------------------------------------------------------------------------
  property p_ostream_val_inactive;
    @(posedge clk) disable iff (reset)
      (!istream_val[grants_index]) |-> (!ostream_val);
  endproperty

  ostream_val_inactive : assert property (p_ostream_val_inactive);


  //-------------------------------------------------------------------------
  // No valid input behavior
  // The output valid signal should be zero if no input is valid
  //-------------------------------------------------------------------------
  property p_no_input_valid;
    @(posedge clk) disable iff (reset)
      if (!(istream_val[0] || istream_val[1] || istream_val[2]))
        ostream_val == 1'b0;
  endproperty

  no_input_valid : assert property (p_no_input_valid);

  //-------------------------------------------------------------------------
  // Selected input valid behavior
  // The selected granted input should always correspond with a valid input
  //-------------------------------------------------------------------------

  property p_selected_input_valid;
    @(posedge clk) disable iff (reset)
      if (istream_val[0] || istream_val[1] || istream_val[2])
        istream_val[grants_index] == 1'b1;
  endproperty

  selected_input_valid : assert property (p_selected_input_valid);

  //-------------------------------------------------------------------------
  // Output valid signal correctness
  // The output valid signal should be the granted input && valid signal
  //-------------------------------------------------------------------------
  property p_ostream_val_correct;
    @(posedge clk) disable iff (reset)
      ostream_val === (istream_val[grants_index] && istream_rdy[grants_index]);
  endproperty

  ostream_val_correct : assert property (p_ostream_val_correct);

  //-------------------------------------------------------------------------
  // Output message correctness
  // The output message should be the granted input message
  //-------------------------------------------------------------------------
  property p_output_message_correct;
    @(posedge clk) disable iff (reset)
      ostream_msg === {grants_index, istream_msg[grants_index]};
  endproperty

  output_message_correct : assert property (p_output_message_correct);



endmodule

bind arbiter_router_Arbiter arbiter_sva u_arbiter_sva (
  .clk(clk),
  .reset(reset),
  .istream_val(istream_val),
  .istream_rdy(istream_rdy),
  .istream_msg(istream_msg),
  .ostream_val(ostream_val),
  .ostream_rdy(ostream_rdy),
  .ostream_msg(ostream_msg)
);
