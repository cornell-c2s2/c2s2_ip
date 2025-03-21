`include "lbist/lbist_controller/lbist_controller.v"

module lbist_controller_sva #(
    parameter int SEED_BITS = 32,
    parameter int SIGNATURE_BITS = 32,
    parameter int NUM_SEEDS = 8,
    parameter int NUM_HASHES = 8,
    parameter int MAX_OUTPUTS_TO_HASH = 32,
    parameter int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH)
)(
    input logic clk,
    input logic reset,
    
    input logic                      lbist_req_val,
    input logic                      lbist_req_rdy,
    input logic                      lbist_resp_val,
    input logic [NUM_SEEDS-1:0]      lbist_resp_msg,
    input logic                      lbist_resp_rdy,
    
    input logic                      lfsr_resp_val,
    input logic [SEED_BITS-1:0]      lfsr_resp_msg,
    input logic                      lfsr_resp_rdy,
    
    input logic                      misr_req_val,
    input logic [MISR_MSG_BITS:0]    misr_req_msg,
    input logic                      misr_req_rdy,
    
    input logic                      misr_resp_val,
    input logic [SIGNATURE_BITS-1:0] misr_resp_msg,
    input logic                      misr_resp_rdy,
    
    input logic                      lfsr_cut_reset
);

    localparam [1:0] IDLE = 2'd0;
    localparam [1:0] START = 2'd1;
    localparam [1:0] COMP_SIG = 2'd2;

    // ==============================================================================
    // State Machine Properties
    // ==============================================================================

    // IDLE state output signals
    property p_idle_outputs;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == IDLE) |-> (
            lbist_req_rdy && !lfsr_resp_val && !misr_req_val && 
            !misr_resp_rdy && !lfsr_cut_reset
        );
    endproperty

    // START state output signals
    property p_start_outputs;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == START) |-> (
            !lbist_req_rdy && lfsr_resp_val && misr_req_val && 
            !misr_resp_rdy && !lfsr_cut_reset
        );
    endproperty

    // COMP_SIG state output signals
    property p_comp_sig_outputs;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == COMP_SIG) |-> (
            !lbist_req_rdy && !lfsr_resp_val && !misr_req_val && 
            misr_resp_rdy && lfsr_cut_reset
        );
    endproperty

    // State Transitions
    property p_idle_to_start;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == IDLE && lbist_req_val && 
         lfsr_resp_rdy && misr_req_rdy) |-> ##1 lbist_controller.state == START;
    endproperty

    property p_start_to_comp_sig;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == START && misr_resp_val) |-> 
        ##1 lbist_controller.state == COMP_SIG;
    endproperty

    // ==============================================================================
    // Counter Properties
    // ==============================================================================
    
    property p_counter_increment;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == COMP_SIG && 
         lbist_controller.counter != NUM_SEEDS - 1) |-> 
        ##1 (lbist_controller.counter == $past(lbist_controller.counter) + 1);
    endproperty

    // ==============================================================================
    // Val/Rdy Protocol Properties
    // ==============================================================================
    
    // Val signals persist until handshake completes
    property p_val_until_handshake(val, rdy);
        @(posedge clk)
        (val && !rdy && !reset) |=> val;
    endproperty
    
    // Verify no premature lbist_resp_val
    property p_no_premature_lbist_resp_val;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == COMP_SIG && 
         lbist_controller.counter != NUM_SEEDS - 1) |-> !lbist_resp_val;
    endproperty

    // ==============================================================================
    // State Transition Properties
    // ==============================================================================
    
    // COMP_SIG to START transition for non-final iterations
    property p_comp_sig_to_start;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == COMP_SIG && 
         lbist_controller.counter != NUM_SEEDS - 1) |-> 
        ##1 lbist_controller.state == START;
    endproperty
    
    // COMP_SIG to IDLE transition for final iteration with handshake
    property p_comp_sig_to_idle;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == COMP_SIG && 
         lbist_controller.counter == NUM_SEEDS - 1 && 
         lbist_resp_val && lbist_resp_rdy) |-> 
        ##1 lbist_controller.state == IDLE;
    endproperty
    
    // Stay in START state until misr_resp_val
    property p_stay_in_start;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == START && !misr_resp_val) |-> 
        ##1 lbist_controller.state == START;
    endproperty
    
    // Stay in COMP_SIG state during final iteration until handshake
    property p_stay_in_comp_sig;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == COMP_SIG && 
         lbist_controller.counter == NUM_SEEDS - 1 && 
         !(lbist_resp_val && lbist_resp_rdy)) |-> 
        ##1 lbist_controller.state == COMP_SIG;
    endproperty

    // ==============================================================================
    // Message Handling Properties
    // ==============================================================================
    
    // Verify LFSR message is correctly set from seeds array
    property p_lfsr_seed_message;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == START) |-> 
        (lfsr_resp_msg == lbist_controller.LFSR_SEEDS[lbist_controller.counter]);
    endproperty
    
    // Verify MISR request message equals NUM_HASHES
    property p_misr_req_message;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == START && misr_req_val) |-> 
        (misr_req_msg == NUM_HASHES);
    endproperty
    
    // ==============================================================================
    // Counter Properties
    // ==============================================================================
    
    // Counter should never exceed maximum value
    property p_counter_max_value;
        @(posedge clk) disable iff (reset)
        lbist_controller.counter < NUM_SEEDS;
    endproperty
    
    // Counter should reset when transitioning to IDLE
    property p_counter_reset_in_idle;
        @(posedge clk) disable iff (reset)
        (lbist_controller.state == COMP_SIG) ##1 (lbist_controller.state == IDLE) |-> 
        ##1 (lbist_controller.counter == 0);
    endproperty
    
    // ==============================================================================
    // lfsr_cut_reset Properties
    // ==============================================================================
    
    // lfsr_cut_reset should only be active in COMP_SIG state
    property p_lfsr_cut_reset_only_in_comp_sig;
        @(posedge clk) disable iff (reset)
        lfsr_cut_reset |-> (lbist_controller.state == COMP_SIG);
    endproperty

    // Assertions
    idle_outputs:          assert property(p_idle_outputs);
    start_outputs:         assert property(p_start_outputs);
    comp_sig_outputs:      assert property(p_comp_sig_outputs);
    idle_to_start:         assert property(p_idle_to_start);
    start_to_comp_sig:     assert property(p_start_to_comp_sig);
    counter_increment:     assert property(p_counter_increment);
    
    // Val/Rdy protocol assertions
    no_early_lbist_resp:   assert property(p_no_premature_lbist_resp_val);
    
    // State transition assertions
    comp_sig_to_start:     assert property(p_comp_sig_to_start);
    comp_sig_to_idle:      assert property(p_comp_sig_to_idle);
    stay_in_start:         assert property(p_stay_in_start);
    stay_in_comp_sig:      assert property(p_stay_in_comp_sig);
    
    // Message handling assertions
    lfsr_seed_message:     assert property(p_lfsr_seed_message);
    misr_req_message:      assert property(p_misr_req_message);
    
    // Counter assertions
    counter_max_value:     assert property(p_counter_max_value);
    counter_reset_in_idle: assert property(p_counter_reset_in_idle);
    
    // lfsr_cut_reset assertions
    lfsr_cut_reset_timing: assert property(p_lfsr_cut_reset_only_in_comp_sig);

endmodule

bind lbist_controller lbist_controller_sva u_lbist_controller_sva (
    .clk(clk),
    .reset(reset),
    .lbist_req_val(lbist_req_val),
    .lbist_req_rdy(lbist_req_rdy),
    .lbist_resp_val(lbist_resp_val),
    .lbist_resp_msg(lbist_resp_msg),
    .lbist_resp_rdy(lbist_resp_rdy),
    .lfsr_resp_val(lfsr_resp_val),
    .lfsr_resp_msg(lfsr_resp_msg),
    .lfsr_resp_rdy(lfsr_resp_rdy),
    .misr_req_val(misr_req_val),
    .misr_req_msg(misr_req_msg),
    .misr_req_rdy(misr_req_rdy),
    .misr_resp_val(misr_resp_val),
    .misr_resp_msg(misr_resp_msg),
    .misr_resp_rdy(misr_resp_rdy),
    .lfsr_cut_reset(lfsr_cut_reset)
);