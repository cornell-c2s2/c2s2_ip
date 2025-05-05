module FPGA_top (
	input logic CLOCK_50,
	inout logic GPIO0,
	input logic GPIO1,
	inout logic GPIO2,
	inout logic GPIO4,
	inout logic GPIO6,
	output logic LEDR0,
	output logic LEDR1
);

assign LEDR0 = GPIO1;
assign LEDR1 = ~GPIO1;

// Generate a clock signal for the FIFO clock
logic ext_clk;

clock_divider #(
  .DIVISOR(2)
) clk_div (
  .clk_in(CLOCK_50),
  .clk_out(ext_clk)
);

tapein2_sp25_top dut(
  .clk(CLOCK_50),
  .reset(GPIO1),
  .clk_out(GPIO5), //
  .cs(GPIO6),
  .mosi(GPIO4),
  .miso(GPIO2),
  .sclk(GPIO0),
  .minion_parity(),
  .adapter_parity(),
  .ext_clk(ext_clk),
  .async_fifo_recv_msg(),
  .async_fifo_recv_val(),
  .async_fifo_recv_rdy(),
  .classifier_send_msg(GPIO7),//
  .classifier_send_val(GPIO9)//
);

endmodule

module clock_divider#(
  parameter int DIVISOR = 2
)
(
  input logic clk_in,
  output logic clk_out
);
  logic [31:0] counter;

  always_ff @(posedge clk_in) begin
    if (counter == DIVISOR - 1) begin
      counter <= 0;
      clk_out <= ~clk_out;
    end else begin
      counter <= counter + 1;
    end
  end

endmodule