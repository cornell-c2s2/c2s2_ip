module lfsr_design 
(   input logic clk, reset,

    //BIST-LFSR interface
    input logic req_val,
    //input [N+4:0] req_msg; //5 MSB = # of loops, 32 LSB = seed
    input logic [36:0] req_msg,
    output logic req_rdy,

    //LFSR-circuit interface
    input logic resq_rdy,
    output logic resq_val,
    output logic [31:0] resq_msg,
    
    );

    //FSM - Design Comms
    lfsr_valready_FSM FSM( 
        .clk(clk), 
        .reset(reset), 
        
        .req_val(req_val), 
        .req_rdy(req_rdy),
        
        .resq_rdy(resq_rdy),
        .resq_val(resq_val),
        .state(state),
        .next_state(next_state)
    );

   
    
    logic [1:0] state;
    logic [1:0] next_state;
    

    //Chain of "DFFs"
    logic [31:0] Q;
    
    //The value coming out of the taps
    logic Q0;
    logic Qin;

    //
    //Shifts Q over by 1 digit, and shifts in the value from taps
    //
    always_ff @(posedge clk || posedge reset) begin 
        if(reset) begin
            Q <= 32'b0;
        end
        else if(state == 1'b10) begin
            Q <= {Q[30:0], Qin};
            Qin <= Q0;
        end
    end

    always_comb begin
        if (req_val) Q = req_msg[31:0];
        else if (resq_rdy) resq_msg = Q;
    end

    //
    // Taps
    //
    wire tap1out;
    wire tap2out;
    wire Q0;

    XOR tap1(.A(Q[1]), .B(Q[5]), .Y(tap1out));
    XOR tap2(.A(Q[6]), .B(Q[31]), .Y(tap2out));
    XOR final_tap(.A(tap1out), .B(tap2out), .Y(Q0));

    






    /*

    NOT USING 
    genvar i;

    generate
        for(i = N-1; i > 0; i = i - 1) begin
            dff d0(.D(Q[i-1]), .Q(Q[i]), .clk(clk), .D0(D0[i]), .D0_en(D0_en));
        end
    endgenerate
    //signal 1

    wire tap1out;
    wire tap2out;
    wire Din;

    XOR tap1(.A(Q[1]), .B(Q[5]), .Y(tap1out));
    XOR tap2(.A(Q[6]), .B(Q[31]), .Y(tap2out));
    XOR final_tap(.A(tap1out), .B(tap2out), .Y(Din));

    dff d_final(.D(Din), .Q(Q[0]), .clk(clk), .D0(D0[0]), .D0_en(D0_en));
    */

endmodule
