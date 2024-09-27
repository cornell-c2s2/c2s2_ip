//================================================
// sine_generator.v
//================================================
`default_nettype none
`ifndef SINE_GENERATOR_V
`define SINE_GENERATOR_V

module SineGenerator #(
  //parameter int Width = 32,
  parameter int initialWidth = 0,
  parameter int workingWidth = 0;
  parameter int phaseWidth = 0;
  parameter int NSTAGES = 0;

) (
  input logic clk,
  input logic reset,

  //output logic recv_rdy,
  //input logic recv_val,
  //input logic [Width - 1:0] recv_msg,

  //input logic send_rdy,
  //output logic send_val,
  //output logic [Width - 1:0] send_msg,

  input logic i_xval,
  input logic i_yval,
  input logic i_phase,
  input logic i_ce,
  output logic o_xval,
  output logic o_yval


);

  wire	signed [(WW-1):0]	e_xval, e_yval;
  assign	e_xval = { {i_xval[(initialWidth-1)]}, i_xval, {(workingWidth-initialWidth-1){1'b0}} };
  assign	e_yval = { {i_yval[(initialWidth-1)]}, i_yval, {(workingWidth-initialWidth-1){1'b0}} };
  
  reg	signed	[(workingWidth-1):0]	xv	[0:(NSTAGES)];
  reg	signed	[(workingWidth-1):0]	yv	[0:(NSTAGES)];
  reg		[(phaseWidth-1):0]	ph	[0:(NSTAGES)];
  
  always @(posedge clk) begin
    case (i_phase[(PW-1):(PW-3)])
      3'b000: begin	// 0 .. 45, No change
        xv[0] <= e_xval;
        yv[0] <= e_yval;
        ph[0] <= i_phase;
      end
      3'b001: begin	// 45 .. 90
        xv[0] <= -e_yval;
        yv[0] <= e_xval;
        ph[0] <= i_phase - 18'h10000;
      end
      3'b010: begin	// 90 .. 135
          xv[0] <= -e_yval;
          yv[0] <= e_xval;
          ph[0] <= i_phase - 18'h10000;
        end
        3'b011: begin	// 135 .. 180
          xv[0] <= -e_xval;
          yv[0] <= -e_yval;
          ph[0] <= i_phase - 18'h20000;
        end
        3'b100: begin	// 180 .. 225
          xv[0] <= -e_xval;
          yv[0] <= -e_yval;
          ph[0] <= i_phase - 18'h20000;
        end
        3'b101: begin	// 225 .. 270
          xv[0] <= e_yval;
          yv[0] <= -e_xval;
          ph[0] <= i_phase - 18'h30000;
        end
        3'b110: begin	// 270 .. 315
          xv[0] <= e_yval;
          yv[0] <= -e_xval;
          ph[0] <= i_phase - 18'h30000;
        end
        3'b111: begin	// 315 .. 360, No change
          xv[0] <= e_xval;
          yv[0] <= e_yval;
          ph[0] <= i_phase;
        end
      endcase
  end
  
  genvar	i;
  generate for(i=0; i<NSTAGES; i=i+1) begin : CORDICops
    always @(posedge i_clk) begin
		  if (ph[i][(PW-1)]) begin
			  xv[i+1] <= xv[i] + (yv[i]>>>(i+1));
			  yv[i+1] <= yv[i] - (xv[i]>>>(i+1));
			  ph[i+1] <= ph[i] + cordic_angle[i];
		  end else begin
			  xv[i+1] <= xv[i] - (yv[i]>>>(i+1));
			  yv[i+1] <= yv[i] + (xv[i]>>>(i+1));
			  ph[i+1] <= ph[i] - cordic_angle[i];
		  end
    end
  end
endgenerate

assign	cordic_angle[ 0] = 18'h0_4b90; //  26.565051 deg
assign	cordic_angle[ 1] = 18'h0_27ec; //  14.036243 deg
assign	cordic_angle[ 2] = 18'h0_1444; //   7.125016 deg
assign	cordic_angle[ 3] = 18'h0_0a2c; //   3.576334 deg
assign	cordic_angle[ 4] = 18'h0_0517; //   1.789911 deg
assign	cordic_angle[ 5] = 18'h0_028b; //   0.895174 deg
assign	cordic_angle[ 6] = 18'h0_0145; //   0.447614 deg
assign	cordic_angle[ 7] = 18'h0_00a2; //   0.223811 deg
assign	cordic_angle[ 8] = 18'h0_0051; //   0.111906 deg
assign	cordic_angle[ 9] = 18'h0_0028; //   0.055953 deg
assign	cordic_angle[10] = 18'h0_0014; //   0.027976 deg
assign	cordic_angle[11] = 18'h0_000a; //   0.013988 deg
assign	cordic_angle[12] = 18'h0_0005; //   0.006994 deg
assign	cordic_angle[13] = 18'h0_0002; //   0.003497 deg

wire	[(WW-1):0]	pre_xval, pre_yval;

assign	pre_xval = xv[NSTAGES] + {{(OW){1'b0}},
	xv[NSTAGES][(WW-OW)],
	{(WW-OW-1){!xv[NSTAGES][WW-OW]}}};
assign	pre_yval = yv[NSTAGES] + {{(OW){1'b0}},
	yv[NSTAGES][(WW-OW)],
	{(WW-OW-1){!yv[NSTAGES][WW-OW]}}};

always @(posedge i_clk) begin
	o_xval <= pre_xval[(WW-1):(WW-OW)];
	o_yval <= pre_yval[(WW-1):(WW-OW)];
end
  //always_comb begin
    //send_msg = recv_msg;
  //end
endmodule

`endif
