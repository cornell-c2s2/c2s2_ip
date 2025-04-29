`include "src/sqrt/sqrt.v"

module SqrtHarness
    #(
        parameter int BIT_WIDTH = 8
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

    Sqrt #(
        .BIT_WIDTH(BIT_WIDTH)
    ) sqrt_inst (
        .reset(reset),
        .clk(clk),
        .recv_msg(recv_msg),
        .recv_val(recv_val),
        .recv_rdy(recv_rdy),
        .send_msg(send_msg),
        .send_val(send_val),
        .send_rdy(send_rdy)
    );

endmodule
