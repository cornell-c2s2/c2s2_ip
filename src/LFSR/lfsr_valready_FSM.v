//Emily Lan
//32-bit FSM, no parametrization
module lfsr_valready_FSM (
    input logic clk,
    input logic reset,
    
    //BIST-LFSR
    input logic req_val,
    output logic req_rdy,

    //LFSR-circuit interface
    input logic resq_rdy,
    output logic resq_val,

    //LFSR
    output logic state,
    output logic next_state

);
    logic [1:0] IDLE = 2'b00, GEN_VAL = 2'b01, SEND_VAL = 2'b10;
    logic [1:0] state, next_state;
    logic [2:0] counter;
    logic counter_reset;

    always_comb begin
        case(state)
            IDLE: begin
                if(req_val) next_state = GEN_VAL;
                else next_state = IDLE;
            end

            GEN_VAL: begin
                if(resq_rdy) next_state = SEND_VAL;
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
        end 
        else begin
            state <= next_state;
        end 
    end

    always_ff @(posedge clk) begin
        if(reset || counter_reset) begin
            counter <= 3'b000;
        end
        else if(state == SEND_VAL) begin
            counter <= counter + 1'b1;
        end
        else begin
            counter <= counter;
        end
    end

endmodule