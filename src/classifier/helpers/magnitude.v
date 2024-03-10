//================================================
// magnitude.v
//================================================
`default_nettype none
`ifndef MAGNITUDE_V
`define MAGNITUDE_V

module magnitude_Magnitude #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES = 8
) (
  input logic [BIT_WIDTH - 1:0] recv_msg [N_SAMPLES - 1:0],
  output logic [BIT_WIDTH - 1:0] send_msg [N_SAMPLES - 1:0]
);

  logic [BIT_WIDTH-1:0] abs_msg [N_SAMPLES-1:0];

  always_comb begin
    for (int i = 0; i < N_SAMPLES; i = i + 1) begin
      if (recv_msg[i][BIT_WIDTH-1]) begin
        abs_msg[i] = -recv_msg[i];
      end else begin
        abs_msg[i] = recv_msg[i];
      end

      send_msg[i] = abs_msg[i];
    end
  end

  
endmodule

`endif
