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

tapein1_sp25_top dut(
  .clk(CLOCK_50),
  .reset(GPIO1),
  .clk_out(GPIO5), //
  .cs(GPIO6),
  .mosi(GPIO4),
  .miso(GPIO2),
  .sclk(GPIO0),
  .minion_parity(),
  .adapter_parity(),
  .ext_clk(CLOCK_50),
  .async_fifo_recv_msg(),
  .async_fifo_recv_val(),
  .async_fifo_recv_rdy(),
  .classifier_send_msg(GPIO7),//
  .classifier_send_val(GPIO9)//
);

endmodule