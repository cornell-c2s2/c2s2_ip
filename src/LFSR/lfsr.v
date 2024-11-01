//Emily Lan
//32-bit FSM, no parametrization
module lfsr(
    input logic clk,
    input logic reset,
    
    //BIST-LFSR
    input logic req_val,
    input logic [37:0] req_msg,
    output logic req_rdy,

    //LFSR-circuit interface
    input logic resq_rdy,
    output logic resq_val,
    output logic [31:0] resq_msg

);

    logic [1:0] IDLE = 2'b00, GEN_VAL = 2'b01, SEND_VAL = 2'b10;
    logic [1:0] state, next_state;
    logic [2:0] counter;
    logic counter_reset;

    logic tap1;
    logic tap2;
    logic final_tap;

    logic [31:0] Q;
    logic load_Q;
    assign load_Q = (state == IDLE && next_state == GEN_VAL);

    //assign final_tap = (resq_msg[1] ^ resq_msg[5]) ^ (resq_msg[6] ^ resq_msg[31]);


    always_comb begin
        case(state)
            IDLE: begin
                if(req_val) next_state = GEN_VAL;
                else next_state = IDLE;
            end

            GEN_VAL: begin
                if(resq_rdy) next_state = SEND_VAL;
                else if(req_val == 0) next_state = IDLE;
                else next_state = GEN_VAL;
            end

            SEND_VAL: begin
                if(counter > 3'b101) next_state = IDLE;
                else if(counter <= 3'b101) next_state = GEN_VAL;
                else next_state = SEND_VAL;
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
                counter_reset = 1'b1;
            end

            GEN_VAL: begin
                req_rdy = 1'b0;
                resq_val = 1'b1; 
                counter_reset = 1'b0;
            end

            SEND_VAL: begin
                req_rdy = 1'b0;
                resq_val = 1'b0;
                counter_reset = 1'b0;
            end
            default: begin
                req_rdy = 1'b0;
                resq_val = 1'b0;
                counter_reset = 1'b0;
            end
        endcase
    end

    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            Q <= 32'b0;
            resq_msg <= 32'b0;
            counter <= 3'b000;
        end 
        else begin
            if(counter_reset) begin
                counter <= 3'b000;
            end
            if(load_Q) begin
                Q <= req_msg[31:0];
                final_tap <= (Q[1] ^ Q[5]) ^ (Q[6] ^ Q[31]);
            end
            if(state == GEN_VAL) final_tap <= (Q[1] ^ Q[5]) ^ (Q[6] ^ Q[31]);
            if(state == SEND_VAL) begin
                counter <= counter + 1'b1;
                resq_msg <= Q;
                //final_tap <= (resq_msg[1] ^ resq_msg[5]) ^ (resq_msg[6] ^ resq_msg[31]);
                Q <= {Q[30:0], final_tap};
            end
            else begin
                counter <= counter;
            end
            state <= next_state;     
        end 
    end

    

endmodule                     