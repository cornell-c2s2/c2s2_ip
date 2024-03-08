//================================================
// magnitude.v
//================================================
`default_nettype none
`ifndef MAGNITUDE_V
`define MAGNITUDE_V

module magnitude_Magnitude #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES = 8,
) (
  input logic [BIT_WIDTH - 1:0] recv_msg [N_SAMPLES - 1:0],
  output logic [BIT_WIDTH - 1:0] send_msg [N_SAMPLES - 1:0]
);

  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
      if (recv_msg[i][BIT_WIDTH-1]) begin
        assign abs_msg[i] = -recv_msg[i];
      end 
      else begin
        assign abs_msg[i] = recv_msg[i];
      end
    end
  endgenerate

  
endmodule

`endif
