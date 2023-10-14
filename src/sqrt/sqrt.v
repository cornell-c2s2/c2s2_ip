`ifndef SQRT
`define SQRT

`include "src/cmn/muxes.v"
`include "src/cmn/regs.v"

// sqrt in Verilog

module Sqrt
    #(
        parameter BIT_WIDTH = 8
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

    logic [BIT_WIDTH-1:0] x;
    logic [BIT_WIDTH-1:0] x_next;    // radicand copy
    logic [BIT_WIDTH-1:0] q;
    logic [BIT_WIDTH-1:0] q_next;    // intermediate root (quotient)
    logic [BIT_WIDTH+1:0] ac;
    logic [BIT_WIDTH+1:0] ac_next;  // accumulator (2 bits wider)
    logic [BIT_WIDTH+1:0] test_res;     // sign test result (2 bits wider)

    always_comb begin
        test_res = ac - {q, 2'b01};
        if (test_res[BIT_WIDTH+1] == 0) begin  // test_res >=0? (check MSB)
            {ac_next, x_next} = {test_res[BIT_WIDTH-1:0], x, 2'b0};
            q_next = {q[BIT_WIDTH-2:0], 1'b1};
        end else begin
            {ac_next, x_next} = {ac[BIT_WIDTH-1:0], x, 2'b0};
            q_next = q << 1;
        end
    end

    localparam ITER = BIT_WIDTH >> 1;   // iterations are half radicand width
    logic [$clog2(ITER)-1:0] i;     // iteration counter

    logic [1:0] currentState;
    logic [1:0] nextState;

    parameter [1:0] IDLE = 2'd0,
                    CALC = 2'd1,
                    DONE = 2'd3;

    // Next State Comb Logic
    always_comb begin
        case (currentState)
        IDLE: if (recv_val && recv_rdy)     nextState = CALC; 
              else                          nextState = IDLE;
        CALC: if (i == ITER-1)              nextState = DONE;
              else                          nextState = CALC; 
        DONE: if (send_rdy && send_val)     nextState = IDLE; 
              else                          nextState = DONE;
        default: nextState = IDLE;
        endcase
    end

    // Output Comb Logic
    always_comb begin
        case (currentState) 
        IDLE:    begin recv_rdy = 1; send_val = 0; end
        CALC:    begin recv_rdy = 0; send_val = 0; end
        DONE:    begin recv_rdy = 0; send_val = 1; end
        default: begin recv_rdy = 'x; send_val = 'x; end
        endcase 
    end

    // State FFs
    always_ff @(posedge clk) begin
        if (reset) begin
        currentState <= IDLE;
        end
        else begin
        currentState <= nextState;
        if (currentState == IDLE) begin
            i <= 0;
            q <= 0;
            {ac, x} <= {{BIT_WIDTH{1'b0}}, recv_msg, 2'b0};
        end
        if (currentState == CALC) begin 
            i <= i + 1;
            q <= q_next;
            x <= x_next;
            ac <= ac_next;
        end
        // if (currentState == DONE) begin 
        //     send_msg <= q;
        // end
        end
    end

    always_comb begin
        if (currentState == DONE) begin 
            send_msg = q;
        end
    end
    
endmodule


/*

module Sqrt
    #(
        parameter BIT_WIDTH = 8
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
    logic [1:0] a_mux_sel;
    logic       x_mux_sel;
    logic       t_mux_sel;
    logic [1:0] q_mux_sel;
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

module control_module 
    #(
        parameter BIT_WIDTH = 8
    )
    (
    input  logic       clk,
    input  logic       reset,

    input  logic       recv_val,
    output logic       recv_rdy,
    output logic       send_val,
    input  logic       send_rdy,

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
        recv_rdy        = table_req_rdy;
        send_val       = table_resp_val;
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

module datapath_module 
    #(
        parameter BIT_WIDTH = 8
    )
    (
    input  logic                 clk,
    input  logic                 reset,

    input  logic [BIT_WIDTH-1:0] recv_msg,

    input  logic [1:0]          a_mux_sel,
    input  logic                x_mux_sel,
    input  logic                t_mux_sel,
    input  logic [1:0]          q_mux_sel,
    input  logic                result_en,

    output logic               t_sign,
    output logic [BIT_WIDTH:0] send_msg
    );

    // Wires
    logic [31:0] out_a_mux;
    logic [31:0] out_shift_a;
    logic [31:0] out_minus;
    logic [31:0] out_shift_x;
    logic [31:0] out_x_mux;
    logic [31:0] out_t_mux;
    logic [31:0] out_q_mux;
    logic [31:0] out_x_reg;
    logic [31:0] out_a_reg;
    logic [31:0] out_t_reg;
    logic [31:0] out_result_reg;
    logic [31:0] out_left_shift;
    logic [31:0] out_q_lsb;

    // a mux
    cmn_Mux3 #(
        .p_nbits(BIT_WIDTH)
    ) a_mux (
        .in0(0),
        .in1(out_shift_a),
        .in2(out_minus),
        .sel(a_mux_sel),
        .out(out_a_mux)
    );

    // x mux
    cmn_Mux2 #(
        .p_nbits(BIT_WIDTH)
    ) x_mux (
        .in0(recv_msg),
        .in1(out_shift_x),
        .sel(x_mux_sel),
        .out(out_x_mux)
    );
    
    // t mux
    cmn_Mux2 #(
        .p_nbits(BIT_WIDTH)
    ) t_mux (
        .in0(0),
        .in1(out_minus),
        .sel(t_mux_sel),
        .out(out_t_mux)
    );

    // q mux
    cmn_Mux3 #(
        .p_nbits(BIT_WIDTH)
    ) q_mux (
        .in0(0),
        .in1(out_q_lsb),
        .in2(out_left_shift),
        .sel(q_mux_sel),
        .out(out_q_mux)
    );

    // x reg
    cmn_Reg #(
        .p_nbits(BIT_WIDTH)
    ) x_reg (
        .clk(clk),
        .q(out_x_reg),
        .d(out_x_mux)
    );

    // a reg
    cmn_Reg #(
        .p_nbits(BIT_WIDTH)
    ) a_reg (
        .clk(clk),
        .q(out_a_reg),
        .d(out_a_mux)
    );

    // t reg
    cmn_Reg #(
        .p_nbits(BIT_WIDTH)
    ) t_reg (
        .clk(clk),
        .q(out_t_reg),
        .d(out_t_mux)
    );

    // result reg
    cmn_EnReg #(
        .p_nbits(BIT_WIDTH)
    ) result_reg (
        .clk(clk),
        .q(out_result_reg),
        .d(out_q_mux),
        .en(result_en)
    );
    
    // left shift
    assign out_left_shift = out_result_reg << 1;

    // set lsb of q to 1
    assign out_q_lsb = {out_left_shift[BIT_WIDTH-1:1], 1'b1};

    // left shift x by two place into a
    logic [BIT_WIDTH+BIT_WIDTH-1:0] shifted_combined;
    assign shifted_combined = {out_a_reg, out_x_reg} << 2;
    assign out_shift_x = shifted_combined[BIT_WIDTH+BIT_WIDTH-1:BIT_WIDTH];
    assign out_shift_a = shifted_combined[BIT_WIDTH-1:0];

    // Do T = A - {Q,01}
    assign out_minus = out_shift_a - {out_result_reg, 2'b01};

    // Output values
    assign t_sign = out_minus[BIT_WIDTH-1];
    assign send_msg = out_result_reg;

endmodule
*/

`endif