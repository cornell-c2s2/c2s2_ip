//================================================
// magnitude.v
//================================================
`default_nettype none
`ifndef MAGNITUDE_V
`define MAGNITUDE_V

module magnitude_Magnitude #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input logic signed [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],
  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES]
);
  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
      assign send_msg[i] = (recv_msg[i] < 0) ? -recv_msg[i] : recv_msg[i];
    end
  endgenerate

endmodule

`endif
