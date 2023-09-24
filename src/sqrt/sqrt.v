`ifndef SQRT
`define SQRT

// sqrt in Verilog

module Sqrt
    #(
        parameter BIT_WIDTH = 32
    )
    (
        input  logic                   reset   ,
        input  logic                   clk     ,

        input  logic [BIT_WIDTH - 1:0] recv_msg,
        input  logic                   recv_val,
        output logic                   recv_rdy,

        output logic [BIT_WIDTH - 1:0] send_msg,
        output logic                   send_val,
        input  logic                   send_rdy
    );

    // Control Signals
    logic [1:0] a_mux_sel,
    logic       x_mux_sel,
    logic       t_mux_sel,
    logic [1:0] q_mux_sel,
    logic       result_en;

    // Data Signals
    logic       t_sign;

    // Control Unit
    control_module ctrl(
        .*
    );

    // Datapath Unit
    datapath_module dpath(
        .*
    );
    
endmodule

//========================================================================
// Control Module
//========================================================================

module control_module (
    input  logic       clk,
    input  logic       reset,

    input  logic       req_val,
    output logic       req_rdy,
    output logic       resp_val,
    input  logic       resp_rdy,

    input  logic       t_sign,

    output logic [1:0] a_mux_sel,
    output logic       x_mux_sel,
    output logic       t_mux_sel,
    output logic [1:0] q_mux_sel,
    output logic       result_en
    );

    logic [1:0] currentState;
    logic [1:0] nextState;

    parameter [1:0] IDLE = 2'd0,
                    CALC = 2'd1,
                    DONE = 2'd3;

    logic [5:0] counter;

    // Next State Comb Logic
    always_comb begin
        case (currentState)
        IDLE: if (recv_val && recv_rdy)     nextState = CALC; 
              else                          nextState = IDLE;
        CALC: if (counter == 0)             nextState = DONE;
              else                          nextState = CALC; 
        DONE: if (send_rdy && send_val)     nextState = IDLE; 
              else                          nextState = DONE;
        default: nextState = IDLE;
        endcase
    end

    // Output Comb Function
    function void output_table
    (
        input logic       table_req_rdy,
        input logic       table_resp_val,
        input logic [1:0] table_a_mux_sel,
        input logic       table_x_mux_sel,
        input logic       table_t_mux_sel,
        input logic [1:0] table_q_mux_sel,
        input logic       table_result_en
    );
    begin
        req_rdy        = table_req_rdy;
        resp_val       = table_resp_val;
        a_mux_sel      = table_a_mux_sel;
        x_mux_sel      = table_x_mux_sel;
        t_mux_sel      = table_t_mux_sel;
        q_mux_sel      = table_q_mux_sel;
        result_en      = table_result_en;
    end
    endfunction

    // Output Comb Logic
    always_comb begin
        case (currentState) 
        //                                    req_rdy, resp_val, a_mux_sel, x_mux_sel, t_mux_sel, q_mux_sel, result_en
        IDLE:                    output_table(      1,        0,         0,         0,         0,         0,         1);
        CALC: if (t_sign == 1)   output_table(      0,        0,         1,         1,         1,         2,         1);
              else               output_table(      0,        0,         2,         1,         1,         1,         1);
        DONE:                    output_table(      0,        1,        'x,        'x,        'x,        'x,        'x);
        default:                 output_table(     'x,       'x,        'x,        'x,        'x,        'x,        'x);
        endcase 
    end

    // State FFs
    always_ff @(posedge clk) begin
        if (reset) begin
        currentState <= IDLE;
        end
        else begin
        currentState <= nextState;
        if (currentState == IDLE) counter <= BIT_WIDTH >> 1;
        if (currentState == CALC) counter <= counter - 1;
        end
    end

endmodule

//========================================================================
// Datapath Module
//========================================================================

module datapath_module (
    input  logic                 clk,
    input  logic                 reset,

    input  logic [BIT_WIDTH-1:0] req_msg,

    input  logic [1:0]          a_mux_sel,
    input  logic                x_mux_sel,
    input  logic                t_mux_sel,
    input  logic [1:0]          q_mux_sel,
    input  logic                result_en

    output logic               t_sign,
    output logic [BIT_WIDTH:0] resp_msg
    );

    // Wires
    logic [31:0] out_a_mux;
    logic [31:0] out_shift_a;
    logic [31:0] out_minus;
    logic [31:0] out_shift_x;
    logic [31:0] out_x_mux;
    logic [31:0] out_a_mux;
    logic [31:0] out_t_mux;
    logic [31:0] out_q_mux;
    logic [31:0] out_x_reg;
    logic [31:0] out_a_reg;
    logic [31:0] out_t_reg;
    logic [31:0] out_result_reg;
    logic [31:0] out_left_shift;

    // a mux
    vc_Mux3 #(
        .p_nbits(BIT_WIDTH)
    ) a_mux (
        .in0(0),
        .in1(out_shift_a),
        .in2(out_minus),
        .sel(a_mux_sel),
        .out(out_a_mux)
    );

    // x mux
    vc_Mux2 #(
        .p_nbits(BIT_WIDTH)
    ) x_mux (
        .in0(recv_msg),
        .in1(out_shift_x),
        .sel(x_mux_sel),
        .out(out_x_mux)
    );
    
    // t mux
    vc_Mux2 #(
        .p_nbits(BIT_WIDTH)
    ) t_mux (
        .in0(0),
        .in1(out_minus),
        .sel(t_mux_sel),
        .out(out_t_mux)
    );

    // q mux
    vc_Mux3 #(
        .p_nbits(BIT_WIDTH)
    ) q_mux (
        .in0(0),
        .in1(out_q_lsb),
        .in2(out_left_shift),
        .sel(q_mux_sel),
        .out(out_q_mux)
    );

    // x reg
    vc_Reg #(
        .p_nbits(BIT_WIDTH)
    ) x_reg (
        .clk(clk),
        .q(out_x_reg),
        .d(out_x_mux)
    );

    // a reg
    vc_Reg #(
        .p_nbits(BIT_WIDTH)
    ) a_reg (
        .clk(clk),
        .q(out_a_reg),
        .d(out_a_mux)
    );

    // t reg
    vc_Reg #(
        .p_nbits(BIT_WIDTH)
    ) t_reg (
        .clk(clk),
        .q(out_t_reg),
        .d(out_t_mux)
    );

    // result reg
    vc_EnReg #(
        .p_nbits(BIT_WIDTH)
    ) result_reg (
        .clk(clk),
        .reset(reset),
        .q(out_result_reg),
        .d(out_q_mux),
        .en(result_en)
    );
    
    // left shift
    assign out_left_shift = out_result_reg << 1;

    // set lsb of q to 1
    assign out_q_lsb = {out_left_shift[BIT_WIDTH-1:1], 1};

    // left shift x by two place into a
    logic [BIT_WIDTH+BIT_WIDTH-1:0] shifted_combined;
    assign shifted_combined = {out_x_reg, out_a_reg} << 2;
    assign out_shift_x = shifted_combined[BIT_WIDTH+BIT_WIDTH-1:BIT_WIDTH];
    assign out_shift_a = shifted_combined[BIT_WIDTH-1:0];

    // Do T = A - {Q,01}
    assign out_minus = out_shift_a - {out_result_reg, 2'b01};

    // Output values
    assign t_sign = out_minus[BIT_WIDTH-1];
    assign resp_msg = out_result_reg;

endmodule

`endif