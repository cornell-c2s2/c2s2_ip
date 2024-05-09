module xbar_and_controller #(
    parameter int BIT_WIDTH = 32,
    parameter int N_INPUTS = 2,
    parameter int N_OUTPUTS = 2,
    localparam int CONTROL_BIT_WIDTH = $clog2(N_INPUTS * N_OUTPUTS),

    parameter int NCONFIGBITS = 4
)
(
    /*xbar ports*/
    input  logic [BIT_WIDTH - 1:0] recv_msg[N_INPUTS],
    input  logic                   recv_val[N_INPUTS],
    output logic                   recv_rdy[N_INPUTS],

    output logic [BIT_WIDTH - 1:0] send_msg[N_OUTPUTS],
    output logic                   send_val[N_OUTPUTS],
    input  logic                   send_rdy[N_OUTPUTS],

    input logic reset,
    input logic clk,

    input  logic [CONTROL_BIT_WIDTH - 1:0] control,
    input  logic                           control_val,
    output logic                           control_rdy,

    /*xbar controller ports*/

    input  logic [BIT_WIDTH - 1:0] recv_msg[N_INPUTS],
    input  logic                   recv_val[N_INPUTS],
    output logic                   recv_rdy[N_INPUTS],

    output logic [BIT_WIDTH - 1:0] send_msg[N_OUTPUTS],
    output logic                   send_val[N_OUTPUTS],
    input  logic                   send_rdy[N_OUTPUTS],

    input logic reset,
    input logic clk,

    input  logic [CONTROL_BIT_WIDTH - 1:0] control,
    input  logic                           control_val,
    output logic                           control_rdy
);

blocking xbar (
    .recv_msg(recv_msg),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),
    .send_msg(send_msg),
    .send_val(send_val),
    .send_rdy(send_rdy),
    .reset(reset),
    .clk(clk),
    .control(/*control*/),
    .control_val(control_val),
    .control_rdy()
);

endmodule