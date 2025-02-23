// Testbench file for the demodulator file

module demodulator_Demodulator_sva #(
  parameter int Width = 32
) (
  input logic clk,
  input logic reset,

  input logic recv_rdy,
  input logic recv_val,
  input logic [Width - 1:0] recv_msg,

  input logic send_rdy,
  input logic send_val,
  input logic [Width - 1:0] send_msg
);
  // we use the sequence syntax to check that 
  property MESSAGE_SEND_PROP;
    @(posedge clk) $past(
        send_msg
    ) == recv_msg;
  endproperty

  MESSAGE_SEND :
  assert property (MESSAGE_SEND_PROP);
endmodule

// Bind statement creates an instance of testbench in the DUT
bind demodulator_Demodulator demodulator_Demodulator_sva demodulator_Demodulator_sva_inst (.*);
