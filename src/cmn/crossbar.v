//========================================================================
// Verilog Components: Crossbar
//========================================================================

`ifndef CMN_PROJECT_CROSSBAR_V
`define CMN_PROJECT_CROSSBAR_V

`include "cmn/queues.v"

module Crossbar
    #(
        parameter BIT_WIDTH = 32, 
        parameter N_INPUTS = 2,
        parameter N_OUTPUTS = 2,
        parameter ADDRESS_BIT_WIDTH = 4,
        parameter BLOCK_ADDRESS = 2
    )
    (
        input  logic [BIT_WIDTH - 1:0] recv_msg [0:N_INPUTS - 1] ,
        input  logic                   recv_val [0:N_INPUTS - 1] ,
        output logic                   recv_rdy [0:N_INPUTS - 1] ,

        output logic [BIT_WIDTH - 1:0] send_msg [0:N_OUTPUTS - 1],
        output logic                   send_val [0:N_OUTPUTS - 1],
        input  logic                   send_rdy [0:N_OUTPUTS - 1],

        input  logic                   reset                     ,
        input  logic                   clk                       ,
        
        input  logic [BIT_WIDTH - 1:0] ctrl_msg                  ,
        input  logic                   ctrl_val                  ,
        output logic                   ctrl_rdy                  
    );

    logic [BIT_WIDTH - 1:0]         stored_control;
    logic [$clog2(N_INPUTS)  - 1:0] input_sel;
    logic [$clog2(N_OUTPUTS) - 1:0] output_sel;
    logic [ADDRESS_BIT_WIDTH - 1:0] block_sel;
    logic                           write;
    logic [BIT_WIDTH - 1:0]         queue_out      [N_INPUTS - 1:0];
    logic                           queue_send_val [N_INPUTS - 1:0];

    assign input_sel  = stored_control[BIT_WIDTH-ADDRESS_BIT_WIDTH-1                    : BIT_WIDTH-ADDRESS_BIT_WIDTH-1-$clog2(N_INPUTS)];
    assign output_sel = stored_control[BIT_WIDTH-ADDRESS_BIT_WIDTH-1-$clog2(N_INPUTS)-1 : BIT_WIDTH-ADDRESS_BIT_WIDTH-1-$clog2(N_INPUTS)-$clog2(N_OUTPUTS)];
    assign block_sel  = ctrl_msg      [BIT_WIDTH-1                                      : BIT_WIDTH-ADDRESS_BIT_WIDTH];
    assign write      = ctrl_msg      [BIT_WIDTH-ADDRESS_BIT_WIDTH                      : BIT_WIDTH-ADDRESS_BIT_WIDTH-1];

    assign ctrl_rdy = 1;

    genvar i;
    generate
        for (i = 0; i < N_INPUTS; i = i+1) begin
            vc_Queue #(
                .p_msg_nbits(BIT_WIDTH), 
                .p_num_msgs(1)
            ) queue_inst (
                .clk(clk),
                .reset(reset),
                .recv_val(recv_val[i]),
                .recv_rdy(recv_rdy[i]),
                .recv_msg(recv_msg[i]),
                .send_val(queue_send_val[i]),
                .send_rdy(send_rdy[output_sel]),
                .send_msg(queue_out[i]),
                .num_free_entries()
            );
        end
    endgenerate


    always @(posedge clk) begin
        if ( reset ) begin
            stored_control <= 0;
        end
        else if( ctrl_val && write ) begin
            stored_control <= ctrl_msg;
        end
    end

    always @(*) begin
        for (integer i = 0; i < N_OUTPUTS; i = i+1) begin
            if ( (i == output_sel)) begin
                send_msg[i] = queue_out[input_sel];
                send_val[i] = queue_send_val[input_sel];
            end
            else begin
                send_msg[i] = 0;
                send_val[i] = 0;
            end
        end

    end
endmodule

`endif /* CMN_PROJECT_CROSSBAR_V */