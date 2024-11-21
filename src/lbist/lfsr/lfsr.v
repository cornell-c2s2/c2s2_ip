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
// IMPORTANT: Do not specify a starting width N of < 4. 
//
// PARAMETERS --------------------------------------------------------
// - N: Bitwidth of LFSR starting seed/LFSR outputs
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
// - resq_val: Valid request to CUT
// - resq_msg: Pseudo-random output to drive CUT
// - resq_rdy: CUT ready to handle another request
// ===================================================================

module lfsr#(
    parameter N = 32,
    parameter T1 = 1,
    parameter T2 = 5,
    parameter T3 = 6,
    parameter T4 = 31
)
(
    input logic clk,
    input logic reset,
    
    //BIST-LFSR interface
    input logic req_val,
    input logic [N-1:0] req_msg,
    output logic req_rdy,

    //LFSR-CUT interface
    input logic resq_rdy,
    output logic resq_val,
    output logic [N-1:0] resq_msg

);

    logic [1:0] IDLE = 2'b00, GEN_VAL = 2'b01, SEND_VAL = 2'b10;
    logic [1:0] state, next_state;

    logic tap1;
    logic tap2;
    logic final_tap;

    logic [N-1:0] Q;
    logic load_Q;
    assign load_Q = (state == IDLE && next_state == GEN_VAL);


    always_comb begin
        case(state)
            IDLE: begin
                if(reset) next_state = IDLE;
                else if(req_val) next_state = GEN_VAL;
                else next_state = IDLE;
            end

            GEN_VAL: begin
                if(reset) next_state = IDLE;
                else if(req_val == 0) next_state = IDLE;
                else if(resq_rdy) next_state = SEND_VAL;
                else next_state = GEN_VAL;
            end

            SEND_VAL: begin
                if(reset) next_state = IDLE;
               else next_state = GEN_VAL;
            end

            default: begin
                next_state = IDLE;
            end
        endcase
    end

    always_comb begin
        case(state)
            IDLE: begin
                req_rdy = 1'b1;
                resq_val = 1'b0;
            end

            GEN_VAL: begin
                req_rdy = 1'b0;
                resq_val = 1'b1; 
            end

            SEND_VAL: begin
                req_rdy = 1'b0;
                resq_val = 1'b0;
            end
            default: begin
                req_rdy = 1'b0;
                resq_val = 1'b0;
            end
        endcase
    end

    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            Q <= {N{1'b0}};
            resq_msg <= {N{1'b0}};
        end 
        else begin
            if(load_Q) begin
                Q <= req_msg;
                final_tap <= ((Q[T2]) ^ (Q[T3] ^ Q[T4])) ^ Q[T1];
            end
            if(state == GEN_VAL) final_tap <= ((Q[T2]) ^ (Q[T3] ^ Q[T4])) ^ Q[T1];

            if(state == SEND_VAL) begin
                resq_msg <= Q;
                Q <= {Q[N-2:0], final_tap};
            end
   
        end 
        state <= next_state; 
    end

    

endmodule
