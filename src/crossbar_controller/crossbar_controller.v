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
        xbarcontrol[3:2] = confignet[1:0];
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


/*

`ifdef FORMAL
  always_comb begin
    if (w == 1'b1 && s == 1'b0) begin
      assert (defaultout == 6'b001001);
    end
    else if (s == 1'b1 && w == 1'b0) begin
      assert (defaultout == 6'b010010);
    end
    else begin
      assert (defaultout == in);
    end
  end
`endif*/
endmodule
