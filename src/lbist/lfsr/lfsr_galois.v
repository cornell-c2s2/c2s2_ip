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
// PARAMETERS --------------------------------------------------------
// - LFSR_MSG_BITS: Bitwidth of LFSR starting seed/LFSR outputs. Must be between 2 and 32 bits.
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

module lfsr_paramver2#(
    parameter LFSR_MSG_BITS = 64
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

     //=========================== LOCAL_PARAMETERS ============================
    // Define taps based on LFSR_MSG_BITS using `if` statements
    int T1;
    int T2;
    int T3;
    int T4;
    localparam int NUM_TAPS = (LFSR_MSG_BITS == 8 || 
                            LFSR_MSG_BITS == 12 || 
                            LFSR_MSG_BITS == 13 || 
                            LFSR_MSG_BITS == 14 || 
                            LFSR_MSG_BITS == 16 || 
                            LFSR_MSG_BITS == 19 || 
                            LFSR_MSG_BITS == 24 || 
                            LFSR_MSG_BITS == 26 || 
                            LFSR_MSG_BITS == 27 || 
                            LFSR_MSG_BITS == 30 || 
                            LFSR_MSG_BITS == 32 ||
                            LFSR_MSG_BITS == 34 || 
                            LFSR_MSG_BITS == 37 || 
                            LFSR_MSG_BITS == 38 || 
                            LFSR_MSG_BITS == 40 || 
                            LFSR_MSG_BITS == 42 ||
                            LFSR_MSG_BITS == 43 ||
                            LFSR_MSG_BITS == 44 ||
                            LFSR_MSG_BITS == 45 ||
                            LFSR_MSG_BITS == 46 ||
                            LFSR_MSG_BITS == 48 ||
                            LFSR_MSG_BITS == 50 ||
                            LFSR_MSG_BITS == 51 ||
                            LFSR_MSG_BITS == 53 ||
                            LFSR_MSG_BITS == 54 ||
                            LFSR_MSG_BITS == 56 ||
                            LFSR_MSG_BITS == 59 ||
                            LFSR_MSG_BITS == 61 ||
                            LFSR_MSG_BITS == 62 ||
                            LFSR_MSG_BITS == 64 ) ? 1 : 0; //0 for 2 taps, 1 for 4 taps

    generate
         if (LFSR_MSG_BITS == 2) begin
            assign T1 = 0;
            assign T2 = 1;
        end
        else if (LFSR_MSG_BITS == 3) begin
            assign T1 = 1;
            assign T2 = 2;
        end
        else if (LFSR_MSG_BITS == 4) begin
            assign T1 = 2;
            assign T2 = 3;
        end
        else if (LFSR_MSG_BITS == 5) begin
            assign T1 = 2;
            assign T2 = 4;
        end
        else if (LFSR_MSG_BITS == 6) begin
            assign T1 = 4;
            assign T2 = 5;
        end
        else if (LFSR_MSG_BITS == 7) begin
            assign T1 = 5;
            assign T2 = 6;
        end
        else if (LFSR_MSG_BITS == 8) begin
            assign T1 = 3;
            assign T2 = 4;
            assign T3 = 5;
            assign T4 = 7;
        end
        else if (LFSR_MSG_BITS == 9) begin
            assign T1 = 4;
            assign T2 = 8;
        end
        else if (LFSR_MSG_BITS == 10) begin
            assign T1 = 6;
            assign T2 = 9;
        end
        else if (LFSR_MSG_BITS == 11) begin
            assign T1 = 8;
            assign T2 = 10;
        end
        else if (LFSR_MSG_BITS == 12) begin
            assign T1 = 5;
            assign T2 = 7;
            assign T3 = 10;
            assign T4 = 11;
        end
        else if (LFSR_MSG_BITS == 13) begin
            assign T1 = 8;
            assign T2 = 9;
            assign T3 = 11;
            assign T4 = 12;
        end
        else if (LFSR_MSG_BITS == 14) begin
            assign T1 = 8;
            assign T2 = 10;
            assign T3 = 12;
            assign T4 = 13;
        end
        else if (LFSR_MSG_BITS == 15) begin
            assign T1 = 13;
            assign T2 = 14;
        end
        else if (LFSR_MSG_BITS == 16) begin
            assign T1 = 10;
            assign T2 = 12;
            assign T3 = 13;
            assign T4 = 15;
        end
        else if (LFSR_MSG_BITS == 17) begin
            assign T1 = 13;
            assign T2 = 16;
        end
        else if (LFSR_MSG_BITS == 18) begin
            assign T1 = 10;
            assign T2 = 17;
        end
        else if (LFSR_MSG_BITS == 19) begin
            assign T1 = 13;
            assign T2 = 16;
            assign T3 = 17;
            assign T4 = 18;
        end
        else if (LFSR_MSG_BITS == 20) begin
            assign T1 = 16;
            assign T2 = 19;
        end
        else if (LFSR_MSG_BITS == 21) begin
            assign T1 = 18;
            assign T2 = 20;
        end
        else if (LFSR_MSG_BITS == 22) begin
            assign T1 = 20;
            assign T2 = 21;
        end
        else if (LFSR_MSG_BITS == 23) begin
            assign T1 = 17;
            assign T2 = 22;
        end
        else if (LFSR_MSG_BITS == 24) begin
            assign T1 = 19;
            assign T2 = 20;
            assign T3 = 22;
            assign T4 = 23;
        end
        else if (LFSR_MSG_BITS == 25) begin
            assign T1 = 21;
            assign T2 = 24;
        end
        else if (LFSR_MSG_BITS == 26) begin
            assign T1 = 19;
            assign T2 = 20;
            assign T3 = 24;
            assign T4 = 25;
        end
        else if (LFSR_MSG_BITS == 27) begin
            assign T1 = 21;
            assign T2 = 22;
            assign T3 = 24;
            assign T4 = 26;
        end
        else if (LFSR_MSG_BITS == 28) begin
            assign T1 = 24;
            assign T2 = 27;
        end
        else if (LFSR_MSG_BITS == 29) begin
            assign T1 = 26;
            assign T2 = 28;
        end
        else if (LFSR_MSG_BITS == 30) begin
            assign T1 = 23;
            assign T2 = 25;
            assign T3 = 27;
            assign T4 = 29;
        end
        else if (LFSR_MSG_BITS == 31) begin
            assign T1 = 27;
            assign T2 = 30;
        end
        else if (LFSR_MSG_BITS == 32) begin
            assign T1 = 24;
            assign T2 = 26;
            assign T3 = 29;
            assign T4 = 31;
        end
        else if (LFSR_MSG_BITS == 33) begin
            assign T1 = 18;
            assign T2 = 32;
        end
        else if (LFSR_MSG_BITS == 34) begin
            assign T1 = 24;
            assign T2 = 28;
            assign T3 = 29;
            assign T4 = 33;
        end
        else if (LFSR_MSG_BITS == 35) begin
            assign T1 = 32;
            assign T2 = 34;
        end
        else if (LFSR_MSG_BITS == 36) begin
            assign T1 = 25;
            assign T2 = 35;
        end
        else if (LFSR_MSG_BITS == 37) begin
            assign T1 = 30;
            assign T2 = 32;
            assign T3 = 33;
            assign T4 = 36;
        end
        else if (LFSR_MSG_BITS == 38) begin
            assign T1 = 31;
            assign T2 = 34;
            assign T3 = 36;
            assign T4 = 37;
        end
        else if (LFSR_MSG_BITS == 39) begin
            assign T1 = 34;
            assign T2 = 38;
        end
        else if (LFSR_MSG_BITS == 40) begin
            assign T1 = 35;
            assign T2 = 37;
            assign T3 = 38;
            assign T4 = 39;
        end
        else if (LFSR_MSG_BITS == 41) begin
            assign T1 = 37;
            assign T2 = 40;
        end
        else if (LFSR_MSG_BITS == 42) begin
            assign T1 = 38;
            assign T2 = 41;
        end
        else if (LFSR_MSG_BITS == 43) begin
            assign T1 = 40;
            assign T2 = 42;
        end
        else if (LFSR_MSG_BITS == 44) begin
            assign T1 = 39;
            assign T2 = 43;
        end
        else if (LFSR_MSG_BITS == 64) begin
            assign T1 = 59;
            assign T2 = 60;
            assign T3 = 62;
            assign T4 = 63;
        end
        
        else begin
            initial $fatal("Unsupported LFSR_MSG_BITS value: %d", LFSR_MSG_BITS);
        end
    endgenerate

    generate
        if(NUM_TAPS == 1'b1) begin
            assign final_tap = ~(Q[T2] ^ Q[T3] ^ Q[T4] ^ Q[T1]);
        end 
        else if(NUM_TAPS == 1'b0) begin
            assign final_tap = (Q[T2] ^ Q[T1]);
        end
        else begin
            initial $fatal("Unsupported NUM_TAPS value: %d", NUM_TAPS);
        end
    endgenerate
        
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