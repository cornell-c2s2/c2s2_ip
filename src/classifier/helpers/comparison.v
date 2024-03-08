//================================================
// comparison.v
//================================================
`default_nettype none
`ifndef COMPARISON_V
`define COMPARISON_V

module comparison_Comparison #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8,
  parameter int CUTOFF_MAG = 20
) (
  input  logic [BIT_WIDTH - 1:0] filtered_valid[N_SAMPLES - 1:0],
  input  logic [BIT_WIDTH - 1:0] mag_in        [N_SAMPLES - 1:0],
  output logic                   compare_out,
  output logic                   done
);

  genvar i;
  always_ff @(posedge clk) begin
    if (reset) begin
      compare_out <= 0;
      done <= 0;
      i <= 0;
    end else if (!done) begin
      if (i < N_SAMPLES) begin
        if (filtered_valid[i] && (mag_in[i] > CUTOFF_MAG)) begin
          compare_out <= 1;
          done <= 1;
          i <= i + 1;
        end else begin
          compare_out <= compare_out;
          done <= done;
          i <= i + 1;
        end
      end else begin
        done <= 1;
      end
    end else begin
      compare_out <= compare_out;
      done <= done;
      i <= i;
    end
  end


endmodule

`endif
