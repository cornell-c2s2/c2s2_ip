//Emily Lan
//32-bit FSM, no parametrization
module lfsr#(
    //Width
    parameter N = 32,
    //Taps
    parameter T1 = 1,
    parameter T2 = 5,
    parameter T3 = 6,
    parameter T4 = 31
)
(
    input logic clk,
    input logic reset,
    
    //BIST-LFSR
    input logic req_val,
    input logic [N-1:0] req_msg,
    output logic req_rdy,

    //LFSR-circuit interface
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