// ===================================================================
// Author: Emily Lan
// Date: 11/17/2024
// Documentation: https://confluence.cornell.edu/display/c2s2/LFSR
//
// Spec: Val/Rdy LFSR implementation. Takes in from the lbist
// controller the starting seed of the LFSR. Then, shifts through the LFSR 
// and returns a unique output due to tapping mechanism. On every clock 
// cycle, starting seed is shifted by 1 and 0th bit is product of taps;
// read documentation for more detail. 
//
// VERY IMPORTANT: Must have 4 taps!!!! Check documentation for bit widths
// that support 4 taps. Common ones include: 8, 16, 24, 30, 32.
// IMPORTANT: Do not specify a starting width LFSR_MSG_BITS of < 4. 
//
// PARAMETERS --------------------------------------------------------
// - LFSR_MSG_BITS: Bitwidth of LFSR starting seed/LFSR outputs
// - T1: Tap #1. For a 32-bit LFSR, T1 = 1
// - T2: Tap #2. For a 32-bit LFSR, T2 = 5
// - T3: Tap #3. For a 32-bit LFSR, T3 = 6
// - T4: Tap #4. For a 32-bit LFSR, T4 = 31
//
// I/O ---------------------------------------------------------------
// - clk
// - reset
// - req_val: Valid packet from BIST controller to LFSR
// - req_msg: Packet (starting seed) from BIST controller
// - req_rdy: LFSR ready to receive packet from BIT controller
// - resp_val: Valid request to CUT
// - resp_msg: Pseudo-random output to drive CUT
// - resp_rdy: CUT ready to handle another request
// ===================================================================

module lfsr#(
    parameter LFSR_MSG_BITS = 32,
    parameter T1 = 1,
    parameter T2 = 5,
    parameter T3 = 6,
    parameter T4 = 31
)
(
    input logic clk,
    input logic reset,

    //BIST-LFSR interface 
    input logic [LFSR_MSG_BITS-1:0] req_msg,
    input logic req_val,
    output logic req_rdy,

    //LFSR-CUT interface
    input logic resp_rdy,
    output logic resp_val,
    output logic [LFSR_MSG_BITS-1:0] resp_msg

);


//============================LOCAL_PARAMETERS=================================
    // State macros
    // IDLE: LFSR is waiting for a valid seed to start generating test vectors
    // GEN_VAL: LFSR computes test vector using shifts + XORs (via taps)
    logic [1:0] IDLE = 2'b00;
    logic [1:0] GEN_VAL = 2'b01;

    // State variables
    logic [1:0] state;
    logic [1:0] next_state;

    // Registers to hold result of Tap/XOR logic
    logic tap1;
    logic tap2;
    logic final_tap;

    // Flip Flop Chain
    logic [LFSR_MSG_BITS-1:0] Q;
    logic [LFSR_MSG_BITS-1:0] next_Q;

    assign final_tap = ((Q[T2]) ^ (Q[T3] ^ Q[T4])) ^ Q[T1];
    assign next_Q = {Q[LFSR_MSG_BITS-2:0], final_tap};

    //================================DATAPATH=====================================
    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            Q <= '0;
        end
        else begin
            if( state == IDLE )          Q <= req_msg;
            else if( state == GEN_VAL ) begin
                if (resp_rdy) Q <= next_Q;
            end
            else                         Q <= Q;
        end
        state <= next_state;
    end

    //===============================CTRL_LOGIC====================================
    // State Transitions
    always_comb begin
        case(state)
            IDLE: begin
                if(reset) next_state = IDLE;
                else if(req_val) next_state = GEN_VAL;
                else next_state = IDLE;
            end

            GEN_VAL: begin
                if(reset) next_state = IDLE;
                else next_state = GEN_VAL;
            end


            default: begin
                next_state = IDLE;
            end
        endcase
    end

    // Set Control Signals
    always_comb begin
        case(state)
            IDLE: begin
                req_rdy = 1'b1;
                resp_val = 1'b0;
                resp_msg = '0;
            end

            GEN_VAL: begin
                req_rdy = 1'b0;
                resp_val = 1'b1;
                resp_msg = Q;
            end

            default: begin
                req_rdy = 1'b0;
                resp_val = 1'b0;
                resp_msg = '0;
            end
        endcase
    end

endmodule
