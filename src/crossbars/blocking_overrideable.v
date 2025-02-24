`ifndef PROJECT_CROSSBAR_V
`define PROJECT_CROSSBAR_V

//Crossbar in Verilog

module crossbars_BlockingOverrideable #(
  parameter int BIT_WIDTH = 32,
  parameter int N_INPUTS = 2,
  parameter int N_OUTPUTS = 2,
  localparam int CONTROL_BIT_WIDTH = $clog2(N_INPUTS * N_OUTPUTS)
) (
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

  //emily's changes
  input logic input_override,
  input logic output_override
);

  logic [CONTROL_BIT_WIDTH - 1:0] stored_control;
  logic [$clog2(N_INPUTS)  - 1:0] input_sel;
  logic [$clog2(N_OUTPUTS) - 1:0] output_sel;

  always_ff @(posedge clk) begin
    if (reset) begin
      stored_control <= 0;
    end else if (control_val) begin
      stored_control <= control;
    end else begin
      stored_control <= stored_control;
    end
  end

  assign control_rdy = 1;

  //emily's changes
  always_comb begin
    input_sel = input_override ? 0 : stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)];

    output_sel = output_override ? 0 : stored_control[
      CONTROL_BIT_WIDTH-$clog2(N_INPUTS)-1 : CONTROL_BIT_WIDTH-$clog2(N_INPUTS)-$clog2(N_OUTPUTS)
    ];
  end

  // demetri's impl
  // always_comb begin
  //   input_sel = stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)];

  //   output_sel = stored_control[CONTROL_BIT_WIDTH-$clog2(
  //       N_INPUTS
  //   )-1 : CONTROL_BIT_WIDTH-$clog2(
  //       N_INPUTS
  //   )-$clog2(
  //       N_OUTPUTS
  //   )];

  //   if (input_override) input_sel = 0;
  //   if (output_override) output_sel = 0;
  // end

  always_comb begin
    for (int i = 0; i < N_OUTPUTS; i = i + 1) begin
      /* verilator lint_off WIDTH */
      if ((i != output_sel)) begin
        /* verilator lint_on WIDTH */
        send_msg[i] = 0;
        send_val[i] = 0;
      end else begin
        send_msg[i] = recv_msg[input_sel];
        send_val[i] = recv_val[input_sel];
      end
    end
    for (int i = 0; i < N_INPUTS; i = i + 1) begin
      /* verilator lint_off WIDTH */
      if ((i != input_sel)) begin
        /* verilator lint_on WIDTH */
        recv_rdy[i] = 0;
      end else begin
        recv_rdy[i] = send_rdy[output_sel];
      end
    end
  end

//fornal verification

`ifdef FORMAL
  always_comb begin
    if (input_override == 1'b1 && output_override == 1'b1) begin
      assert (input_sel == 0 && output_sel == 0);
    end
    else if (input_override == 1'b1 && output_override == 1'b0) begin
      assert (input_sel == 0 && output_sel == output_sel = stored_control[CONTROL_BIT_WIDTH-$clog2(
            N_INPUTS
        )-1 : CONTROL_BIT_WIDTH-$clog2(
            N_INPUTS
        )-$clog2(
            N_OUTPUTS
        )]);
    end
    else if (input_override == 1'b0 && output_override == 1'b1) begin
      assert (input_sel == stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)]
      && output_sel == 0);
    end
    else if (input_override == 1'b0 && output_override == 1'b0) begin
      assert (input_sel == stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)] &&
        output_sel = stored_control[CONTROL_BIT_WIDTH-$clog2(
            N_INPUTS
        )-1 : CONTROL_BIT_WIDTH-$clog2(
            N_INPUTS
        )-$clog2(
            N_OUTPUTS
        )]);
    end
    else begin
      assert (input_sel == stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)] &&
        output_sel = stored_control[CONTROL_BIT_WIDTH-$clog2(
            N_INPUTS
        )-1 : CONTROL_BIT_WIDTH-$clog2(
            N_INPUTS
        )-$clog2(
            N_OUTPUTS
        )]);
    end
  end
`endif


endmodule

`endif

