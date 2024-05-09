module crossbar_controller #(
  parameter int NCONFIGBITS = 4
)
(
  input logic [(NCONFIGBITS-1): 0] confignet,
  input logic gpio1,
  input logic gpio2,
  output logic [(NCONFIGBITS-1) : 0] xbarcontrol
);

  /*
  if gpio1 is high, SPI = input, if gpio2 is high, SPI = output

  i have it set to:
    spi = 00
    router = 10
  */
  /*
  input [3:0] confignet;
  input gpio1;
  input gpio2;
  output [3:0] xbarcontrol;
  */
  wire [1:0] gpioconfig;
  assign gpioconfig = {gpio1, gpio2};

  always_comb begin
    case(gpioconfig)
      2'b11: begin
        xbarcontrol[3:2] = 2'b00;
        xbarcontrol[1:0] = 2'b00;
      end
      2'b10: begin
        xbarcontrol[3:2] = 2'b00;
        xbarcontrol[1:0] = confignet[1:0];
      end
      2'b01: begin
        xbarcontrol[3:2] = confignet[3:2];
        xbarcontrol[1:0] = 2'b00;
      end
      2'b00: begin
        xbarcontrol = confignet;
      end
      default: begin
        xbarcontrol = confignet;
      end
    endcase
  end




`ifdef FORMAL
  always_comb begin
    if (gpio1 == 1'b1 && gpio2 == 1'b1) begin
      assert (xbarcontrol == 4'b0000);
    end
    else if (gpio1 == 1'b1 && gpio2 == 1'b0) begin
      assert (xbarcontrol[3:2] == 2'b00 && xbarcontrol[1:0] == confignet[1:0]);
    end
    else if (gpio1 == 1'b0 && gpio2 == 1'b1) begin
      assert (xbarcontrol[3:2] ==  confignet[3:2] && xbarcontrol[1:0] == 2'b00);
    end
    else if (gpio1 == 1'b0 && gpio2 == 1'b0) begin
      assert (xbarcontrol[3:2] ==  confignet[3:2] && xbarcontrol[1:0] == confignet[1:0]);
    end
    else begin
      assert (xbarcontrol == confignet);
    end
  end
`endif
endmodule
