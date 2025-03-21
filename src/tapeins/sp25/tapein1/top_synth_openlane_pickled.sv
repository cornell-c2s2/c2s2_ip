`line 1 "top_synth_openlane.sv" 1

`line 2 "top_synth_openlane.sv" 0
 
`line 2 "top_synth_openlane.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
 
 

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
 
 
 

`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
 

`line 14 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 14 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 1
 
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 1
 
 
 
 

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
 
 

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
 
`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 




`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 
 

`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 








`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 
 

`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 





`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 
 

`line 44 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 








`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
   


`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 2
`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0


`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
module cmn_Reg #(
  parameter p_nbits = 1
) (
  input  logic               clk,   
  output logic [p_nbits-1:0] q,     
  input  logic [p_nbits-1:0] d      
);

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  always_ff @(posedge clk) q <= d;

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
endmodule

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
module cmn_ResetReg #(
  parameter p_nbits       = 1,
  parameter p_reset_value = 0
) (
  input  logic               clk,     
  input  logic               reset,   
  output logic [p_nbits-1:0] q,       
  input  logic [p_nbits-1:0] d        
);

`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  always_ff @(posedge clk) q <= reset ? p_reset_value : d;

`line 49 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
endmodule

`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 55 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
module cmn_EnReg #(
  parameter p_nbits = 1
) (
  input  logic               clk,   
  output logic [p_nbits-1:0] q,     
  input  logic [p_nbits-1:0] d,     
  input  logic               en     
);

`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  always_ff @(posedge clk) if (en) q <= d;

`line 66 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
endmodule

`line 68 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
module cmn_EnResetReg #(
  parameter p_nbits       = 1,
  parameter p_reset_value = 0
) (
  input  logic               clk,     
  input  logic               reset,   
  output logic [p_nbits-1:0] q,       
  input  logic [p_nbits-1:0] d,       
  input  logic               en       
);

`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  always_ff @(posedge clk) if (reset || en) q <= reset ? p_nbits'(p_reset_value) : d;

`line 85 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
endmodule

`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
   


`line 90 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 2
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_Mux2 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  input  logic               sel,
  output logic [p_nbits-1:0] out
);

`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  always_comb begin
    case (sel)
      1'd0: out = in0;
      1'd1: out = in1;
      default: out = {p_nbits{1'bx}};
    endcase
  end

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_Mux3 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  input  logic [        1:0] sel,
  output logic [p_nbits-1:0] out
);

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  always_comb begin
    case (sel)
      2'd0: out = in0;
      2'd1: out = in1;
      2'd2: out = in2;
      default: out = {p_nbits{1'bx}};
    endcase
  end

`line 54 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 60 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_Mux4 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  input  logic [        1:0] sel,
  output logic [p_nbits-1:0] out
);

`line 71 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  always_comb begin
    case (sel)
      2'd0: out = in0;
      2'd1: out = in1;
      2'd2: out = in2;
      2'd3: out = in3;
      default: out = {p_nbits{1'bx}};
    endcase
  end

`line 81 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_Mux5 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

`line 99 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      default: out = {p_nbits{1'bx}};
    endcase
  end

`line 110 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 112 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 116 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_Mux6 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

`line 129 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      default: out = {p_nbits{1'bx}};
    endcase
  end

`line 141 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 143 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 147 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_Mux7 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  in6,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

`line 161 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      3'd6: out = in6;
      default: out = {p_nbits{1'bx}};
    endcase
  end

`line 174 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 176 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 180 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_Mux8 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  in2,
  in3,
  in4,
  in5,
  in6,
  in7,
  input  logic [        2:0] sel,
  output logic [p_nbits-1:0] out
);

`line 195 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  always_comb begin
    case (sel)
      3'd0: out = in0;
      3'd1: out = in1;
      3'd2: out = in2;
      3'd3: out = in3;
      3'd4: out = in4;
      3'd5: out = in5;
      3'd6: out = in6;
      3'd7: out = in7;
      default: out = {p_nbits{1'bx}};
    endcase
  end

`line 209 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 211 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 
 

`line 215 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
module cmn_MuxN
#(
  parameter nbits = 1,
  parameter ninputs = 2
)(
  input  logic               [nbits-1:0]   in   [0:ninputs-1], 
  input  logic     [$clog2(ninputs)-1:0]   sel,
  output logic               [nbits-1:0]   out
);

`line 225 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  assign out = in[sel];

`line 227 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
endmodule

`line 229 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  


`line 232 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 2
`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 10 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
`line 10 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 





`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 








`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 












`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 









`line 44 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 








`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
   


`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 2
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0


`line 10 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
 
 

`line 14 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
module cmn_Regfile_1r1w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   
  parameter c_addr_nbits = $clog2(p_num_entries)
) (
  input logic clk,

`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [c_addr_nbits-1:0] read_addr,
  output logic [p_data_nbits-1:0] read_data,

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input logic                    write_en,
  input logic [c_addr_nbits-1:0] write_addr,
  input logic [p_data_nbits-1:0] write_data
);

`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 39 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  assign read_data = rfile[read_addr];

`line 41 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  always_ff @(posedge clk) if (write_en) rfile[write_addr] <= write_data;

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 

`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
endmodule

`line 66 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
 
 

`line 70 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
module cmn_ResetRegfile_1r1w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,
  parameter p_reset_value = 0,

`line 75 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   
  parameter c_addr_nbits = $clog2(p_num_entries)
) (
  input logic clk,
  input logic reset,

`line 81 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [c_addr_nbits-1:0] read_addr,
  output logic [p_data_nbits-1:0] read_data,

`line 86 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 88 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input logic                    write_en,
  input logic [c_addr_nbits-1:0] write_addr,
  input logic [p_data_nbits-1:0] write_data
);

`line 93 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

`line 95 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 97 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  assign read_data = rfile[read_addr];

`line 99 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   
   

`line 102 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  genvar i;
  generate
    for (i = 0; i < p_num_entries; i = i + 1) begin : wport
      always_ff @(posedge clk)
        if (reset) rfile[i] <= p_reset_value;
        else if (write_en && (i[c_addr_nbits-1:0] == write_addr)) rfile[i] <= write_data;
    end
  endgenerate

`line 111 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 113 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 

`line 130 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
endmodule

`line 132 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
 
 

`line 136 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
module cmn_Regfile_2r1w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,

`line 140 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   
  parameter c_addr_nbits = $clog2(p_num_entries)
) (
  input logic clk,

`line 145 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 147 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [c_addr_nbits-1:0] read_addr0,
  output logic [p_data_nbits-1:0] read_data0,

`line 150 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 152 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [c_addr_nbits-1:0] read_addr1,
  output logic [p_data_nbits-1:0] read_data1,

`line 155 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 157 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input logic                    write_en,
  input logic [c_addr_nbits-1:0] write_addr,
  input logic [p_data_nbits-1:0] write_data
);

`line 162 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

`line 164 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 166 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  assign read_data0 = rfile[read_addr0];
  assign read_data1 = rfile[read_addr1];

`line 169 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 171 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  always_ff @(posedge clk) if (write_en) rfile[write_addr] <= write_data;

`line 173 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 175 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 

`line 192 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
endmodule

`line 194 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
 
 

`line 198 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
module cmn_Regfile_2r2w #(
  parameter p_data_nbits  = 1,
  parameter p_num_entries = 2,

`line 202 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   
  parameter c_addr_nbits = $clog2(p_num_entries)
) (
  input logic clk,

`line 207 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 209 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [c_addr_nbits-1:0] read_addr0,
  output logic [p_data_nbits-1:0] read_data0,

`line 212 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 214 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [c_addr_nbits-1:0] read_addr1,
  output logic [p_data_nbits-1:0] read_data1,

`line 217 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 219 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input logic                    write_en0,
  input logic [c_addr_nbits-1:0] write_addr0,
  input logic [p_data_nbits-1:0] write_data0,

`line 223 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 225 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input logic                    write_en1,
  input logic [c_addr_nbits-1:0] write_addr1,
  input logic [p_data_nbits-1:0] write_data1
);

`line 230 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  logic [p_data_nbits-1:0] rfile[p_num_entries-1:0];

`line 232 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 234 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  assign read_data0 = rfile[read_addr0];
  assign read_data1 = rfile[read_addr1];

`line 237 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 239 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  always_ff @(posedge clk) begin

`line 241 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
    if (write_en0) rfile[write_addr0] <= write_data0;

`line 243 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
    if (write_en1) rfile[write_addr1] <= write_data1;

`line 245 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  end

`line 247 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   

`line 249 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  
`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0

`line 276 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 

`line 278 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
endmodule

`line 280 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
 
 
 

`line 284 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
module cmn_Regfile_2r1w_zero (
  input logic clk,

`line 287 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [ 4:0] rd_addr0,
  output logic [31:0] rd_data0,

`line 290 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input  logic [ 4:0] rd_addr1,
  output logic [31:0] rd_data1,

`line 293 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  input logic        wr_en,
  input logic [ 4:0] wr_addr,
  input logic [31:0] wr_data
);

`line 298 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   
   

`line 301 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  logic [31:0] rf_read_data0;
  logic [31:0] rf_read_data1;

`line 304 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
  cmn_Regfile_2r1w #(
    .p_data_nbits (32),
    .p_num_entries(32)
  ) r_file (
    .clk       (clk),
    .read_addr0(rd_addr0),
    .read_data0(rf_read_data0),
    .read_addr1(rd_addr1),
    .read_data1(rf_read_data1),
    .write_en  (wr_en),
    .write_addr(wr_addr),
    .write_data(wr_data)
  );

`line 318 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   
  assign rd_data0 = (rd_addr0 == 5'd0) ? 32'd0 : rf_read_data0;
  assign rd_data1 = (rd_addr1 == 5'd0) ? 32'd0 : rf_read_data1;

`line 322 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
endmodule

`line 324 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 0
   


`line 327 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regfiles.v" 2
`line 10 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 
 





`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 








`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 












`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 









`line 44 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
 








`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 0
   


`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/assert.v" 2
`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0


`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 

`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 

`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 
 
 
 
 
 
 
 
 
 

`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
module cmn_QueueCtrl1 #(
  parameter p_type = 4'b0000
) (
  input logic clk,
  input logic reset,

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  input  logic enq_val,   
  output logic enq_rdy,   

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  output logic deq_val,   
  input  logic deq_rdy,   

`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  output logic write_en,          
  output logic bypass_mux_sel,    
  output logic num_free_entries   
);

`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic full;
  logic full_next;

`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  always_ff @(posedge clk) begin
    full <= reset ? 1'b0 : full_next;
  end

`line 60 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign num_free_entries = full ? 1'b0 : 1'b1;

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  localparam c_pipe_en = |(p_type & 4'b0001);
  localparam c_bypass_en = |(p_type & 4'b0010);

`line 67 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 69 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_enq;
  assign do_enq = enq_rdy && enq_val;

`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_deq;
  assign do_deq = deq_rdy && deq_val;

`line 75 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   

`line 78 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic empty;
  assign empty = ~full;

`line 81 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_pipe;
  assign do_pipe = c_pipe_en && full && do_enq && do_deq;

`line 84 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_bypass;
  assign do_bypass      = c_bypass_en && empty && do_enq && do_deq;

`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign write_en       = do_enq && ~do_bypass;

`line 89 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   
   

`line 93 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign bypass_mux_sel = empty;

`line 95 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   
   
   
   

`line 101 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign enq_rdy        = ~full || (c_pipe_en && full && deq_rdy);
  assign deq_val        = ~empty || (c_bypass_en && empty && enq_val);

`line 104 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 106 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign full_next      = (do_deq && ~do_pipe) ? 1'b0 : (do_enq && ~do_bypass) ? 1'b1 : full;

`line 108 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
endmodule

`line 110 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 
 
 

`line 116 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
module cmn_QueueDpath1 #(
  parameter p_type      = 4'b0000,
  parameter p_msg_nbits = 1
) (
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   write_en,
  input  logic                   bypass_mux_sel,
  input  logic [p_msg_nbits-1:0] enq_msg,
  output logic [p_msg_nbits-1:0] deq_msg
);

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 130 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [p_msg_nbits-1:0] qstore;

`line 132 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  cmn_EnResetReg #(p_msg_nbits) qstore_reg (
    .clk  (clk),
    .reset(reset),
    .en   (write_en),
    .d    (enq_msg),
    .q    (qstore)
  );

`line 140 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 142 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  generate
    if (|(p_type & 4'b0010))

`line 145 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      cmn_Mux2 #(p_msg_nbits) bypass_mux (
        .in0(qstore),
        .in1(enq_msg),
        .sel(bypass_mux_sel),
        .out(deq_msg)
      );

`line 152 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    else begin
      logic unused = &{1'b0, bypass_mux_sel, 1'b0};
      assign deq_msg = qstore;
    end
  endgenerate

`line 158 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
endmodule

`line 160 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 
 
 
 
 
 
 
 
 
 

`line 173 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
module cmn_QueueCtrl #(
  parameter p_type     = 4'b0000,
  parameter p_num_msgs = 2,

`line 177 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
  parameter c_addr_nbits = $clog2(p_num_msgs)
) (
  input logic clk,
  reset,

`line 183 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  input  logic enq_val,   
  output logic enq_rdy,   

`line 186 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  output logic deq_val,   
  input  logic deq_rdy,   

`line 189 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  output logic                    write_en,          
  output logic [c_addr_nbits-1:0] write_addr,        
  output logic [c_addr_nbits-1:0] read_addr,         
  output logic                    bypass_mux_sel,    
  output logic [  c_addr_nbits:0] num_free_entries   
);

`line 196 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 198 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [c_addr_nbits-1:0] enq_ptr;
  logic [c_addr_nbits-1:0] enq_ptr_next;

`line 201 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  cmn_ResetReg #(c_addr_nbits) enq_ptr_reg (
    .clk  (clk),
    .reset(reset),
    .d    (enq_ptr_next),
    .q    (enq_ptr)
  );

`line 208 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [c_addr_nbits-1:0] deq_ptr;
  logic [c_addr_nbits-1:0] deq_ptr_next;

`line 211 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  cmn_ResetReg #(c_addr_nbits) deq_ptr_reg (
    .clk  (clk),
    .reset(reset),
    .d    (deq_ptr_next),
    .q    (deq_ptr)
  );

`line 218 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign write_addr = enq_ptr;
  assign read_addr  = deq_ptr;

`line 221 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 223 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic full;
  logic full_next;

`line 226 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  cmn_ResetReg #(1) full_reg (
    .clk  (clk),
    .reset(reset),
    .d    (full_next),
    .q    (full)
  );

`line 233 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 235 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  localparam c_pipe_en = |(p_type & 4'b0001);
  localparam c_bypass_en = |(p_type & 4'b0010);

`line 238 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 240 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_enq;
  assign do_enq = enq_rdy && enq_val;

`line 243 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_deq;
  assign do_deq = deq_rdy && deq_val;

`line 246 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   

`line 249 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic empty;
  assign empty = ~full && (enq_ptr == deq_ptr);

`line 252 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_pipe;
  assign do_pipe = c_pipe_en && full && do_enq && do_deq;

`line 255 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic do_bypass;
  assign do_bypass = c_bypass_en && empty && do_enq && do_deq;

`line 258 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign write_en = do_enq && ~do_bypass;

`line 260 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   
   

`line 264 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign bypass_mux_sel = empty;

`line 266 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   
   
   
   

`line 272 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign enq_rdy = ~full || (c_pipe_en && full && deq_rdy);
  assign deq_val = ~empty || (c_bypass_en && empty && enq_val);

`line 275 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 277 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [c_addr_nbits-1:0] deq_ptr_plus1;
  assign deq_ptr_plus1 = deq_ptr + 1'b1;

`line 280 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  /*verilator lint_off WIDTH*/ 

`line 282 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [c_addr_nbits-1:0] deq_ptr_inc;
  assign deq_ptr_inc = (deq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : deq_ptr_plus1;

`line 285 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [c_addr_nbits-1:0] enq_ptr_plus1;
  assign enq_ptr_plus1 = enq_ptr + 1'b1;

`line 288 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [c_addr_nbits-1:0] enq_ptr_inc;
  assign enq_ptr_inc = (enq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : enq_ptr_plus1;

`line 291 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  /*verilator lint_on WIDTH*/ 

`line 293 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign deq_ptr_next = (do_deq && ~do_bypass) ? (deq_ptr_inc) : deq_ptr;

`line 295 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign enq_ptr_next = (do_enq && ~do_bypass) ? (enq_ptr_inc) : enq_ptr;

`line 297 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign full_next
    = ( do_enq && ~do_deq && ( enq_ptr_inc == deq_ptr ) ) ? 1'b1
    : ( do_deq && full && ~do_pipe )                      ? 1'b0
    :                                                       full;

`line 302 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 304 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  assign num_free_entries
    = full                ? {(c_addr_nbits+1){1'b0}}
    : empty               ? p_num_msgs[c_addr_nbits:0]
    : (enq_ptr > deq_ptr) ? p_num_msgs[c_addr_nbits:0] - (enq_ptr - deq_ptr)
    : (deq_ptr > enq_ptr) ? deq_ptr - enq_ptr
    :                       {(c_addr_nbits+1){1'bx}};

`line 311 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
endmodule

`line 313 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 
 
 

`line 319 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
module cmn_QueueDpath #(
  parameter p_type      = 4'b0000,
  parameter p_msg_nbits = 4,
  parameter p_num_msgs  = 2,

`line 324 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
  parameter c_addr_nbits = $clog2(p_num_msgs)
) (
  input  logic                    clk,
  input  logic                    write_en,
  input  logic                    bypass_mux_sel,
  input  logic [c_addr_nbits-1:0] write_addr,
  input  logic [c_addr_nbits-1:0] read_addr,
  input  logic [ p_msg_nbits-1:0] enq_msg,
  output logic [ p_msg_nbits-1:0] deq_msg
);

`line 336 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 338 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  logic [p_msg_nbits-1:0] read_data;

`line 340 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  cmn_Regfile_1r1w #(p_msg_nbits, p_num_msgs) qstore (
    .clk       (clk),
    .read_addr (read_addr),
    .read_data (read_data),
    .write_en  (write_en),
    .write_addr(write_addr),
    .write_data(enq_msg)
  );

`line 349 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 351 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  generate
    if (|(p_type & 4'b0010))

`line 354 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      cmn_Mux2 #(p_msg_nbits) bypass_mux (
        .in0(read_data),
        .in1(enq_msg),
        .sel(bypass_mux_sel),
        .out(deq_msg)
      );

`line 361 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    else begin
      logic unused = 1'b0 & bypass_mux_sel;
      assign deq_msg = read_data;
    end
  endgenerate

`line 367 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
endmodule

`line 369 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 

`line 373 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
module cmn_Queue #(
  parameter p_type      = 4'b0000,
  parameter p_msg_nbits = 1,
  parameter p_num_msgs  = 2,

`line 378 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
  parameter c_addr_nbits = $clog2(p_num_msgs)
) (
  input logic clk,
  input logic reset,

`line 384 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  input  logic                   enq_val,
  output logic                   enq_rdy,
  input  logic [p_msg_nbits-1:0] enq_msg,

`line 388 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  output logic                   deq_val,
  input  logic                   deq_rdy,
  output logic [p_msg_nbits-1:0] deq_msg,

`line 392 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  output logic [c_addr_nbits:0] num_free_entries
);

`line 395 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  generate
    if (p_num_msgs == 1) begin

`line 398 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      logic write_en;
      logic bypass_mux_sel;

`line 401 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      cmn_QueueCtrl1 #(p_type) ctrl (
        .clk             (clk),
        .reset           (reset),
        .enq_val         (enq_val),
        .enq_rdy         (enq_rdy),
        .deq_val         (deq_val),
        .deq_rdy         (deq_rdy),
        .write_en        (write_en),
        .bypass_mux_sel  (bypass_mux_sel),
        .num_free_entries(num_free_entries)
      );

`line 413 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      cmn_QueueDpath1 #(p_type, p_msg_nbits) dpath (
        .clk           (clk),
        .reset         (reset),
        .write_en      (write_en),
        .bypass_mux_sel(bypass_mux_sel),
        .enq_msg       (enq_msg),
        .deq_msg       (deq_msg)
      );

`line 422 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    end else begin

`line 424 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      logic                    write_en;
      logic                    bypass_mux_sel;
      logic [c_addr_nbits-1:0] write_addr;
      logic [c_addr_nbits-1:0] read_addr;

`line 429 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      cmn_QueueCtrl #(p_type, p_num_msgs) ctrl (
        .clk             (clk),
        .reset           (reset),
        .enq_val         (enq_val),
        .enq_rdy         (enq_rdy),
        .deq_val         (deq_val),
        .deq_rdy         (deq_rdy),
        .write_en        (write_en),
        .write_addr      (write_addr),
        .read_addr       (read_addr),
        .bypass_mux_sel  (bypass_mux_sel),
        .num_free_entries(num_free_entries)
      );

`line 443 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      cmn_QueueDpath #(p_type, p_msg_nbits, p_num_msgs) dpath (
        .clk           (clk),
        .write_en      (write_en),
        .bypass_mux_sel(bypass_mux_sel),
        .write_addr    (write_addr),
        .read_addr     (read_addr),
        .enq_msg       (enq_msg),
        .deq_msg       (deq_msg)
      );

`line 453 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    end
  endgenerate

`line 456 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 458 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 

`line 469 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   

`line 471 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
  
   
   
  
   
   
  
   
   
   
   
  
   
   

`line 487 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   

`line 490 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
endmodule

`line 492 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   


`line 495 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 2
`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0


`line 14 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
module spi_helpers_Minion_Adapter #(
  parameter int nbits = 8,
  parameter int num_entries = 1
) (
  input  logic             clk,
  input  logic             reset,
  input  logic             pull_en,
  output logic             pull_msg_val,
  output logic             pull_msg_spc,
  output logic [nbits-3:0] pull_msg_data,
  input  logic             push_en,
  input  logic             push_msg_val_wrt,   
  input  logic             push_msg_val_rd,    
  input  logic [nbits-3:0] push_msg_data,
  input  logic [nbits-3:0] recv_msg,
  output logic             recv_rdy,
  input  logic             recv_val,
  output logic [nbits-3:0] send_msg,
  input  logic             send_rdy,
  output logic             send_val,
  output logic             parity
);

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
  logic                         open_entries;

`line 39 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
  logic [            nbits-3:0] cm_q_send_msg;
  logic                         cm_q_send_rdy;
  logic                         cm_q_send_val;
  logic [$clog2(num_entries):0] unused;

`line 44 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
  cmn_Queue #(4'b0, nbits - 2, num_entries) cm_q (
    .clk(clk),
    .num_free_entries(unused),
    .reset(reset),
    .enq_msg(recv_msg),
    .enq_rdy(recv_rdy),
    .enq_val(recv_val),
    .deq_msg(cm_q_send_msg),
    .deq_rdy(cm_q_send_rdy),
    .deq_val(cm_q_send_val)
  );

`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
  logic [$clog2(num_entries):0] mc_q_num_free;
  logic                         mc_q_recv_rdy;
  logic                         mc_q_recv_val;

`line 60 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
  cmn_Queue #(4'b0, nbits - 2, num_entries) mc_q (
    .clk(clk),
    .num_free_entries(mc_q_num_free),
    .reset(reset),
    .enq_msg(push_msg_data),
    .enq_rdy(mc_q_recv_rdy),
    .enq_val(mc_q_recv_val),
    .deq_msg(send_msg),
    .deq_rdy(send_rdy),
    .deq_val(send_val)
  );

`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
  assign parity = (^send_msg) & send_val;

`line 74 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
  always_comb begin : comb_block
    open_entries  = mc_q_num_free > 1;
    mc_q_recv_val = push_msg_val_wrt & push_en;
    pull_msg_spc  = mc_q_recv_rdy & ((~mc_q_recv_val) | open_entries);
    cm_q_send_rdy = push_msg_val_rd & pull_en;
    pull_msg_val  = cm_q_send_rdy & cm_q_send_val;
    pull_msg_data = cm_q_send_msg & {(nbits - 2) {pull_msg_val}};
  end

`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 0
endmodule



`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_adapter.v" 2
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0

`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
 
 
 
 

`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
 

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
 
`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 1

`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0
 
 
 
 
 

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0
 
module regs_shift_Bitwise #(
  parameter int p_nbits = 8,
  parameter bit p_reset_value = 0
) (
  input  logic               clk,       
  input  logic               reset,     
  input  logic               d,         
  input  logic               en,        
  input  logic [p_nbits-1:0] load,      
  input  logic               load_en,   
  output logic [p_nbits-1:0] q          
);

`line 41 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 0
  always_ff @(posedge clk) begin
    if (reset) begin
      q <= {p_nbits{p_reset_value}};
    end else if (load_en) begin
      q <= load;
    end else if ((~load_en) & en) begin
      q <= {q[p_nbits-2:0], d};
    end else begin
      q <= q;
    end
  end
endmodule



`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/regs/shift/bitwise.v" 2
`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0

`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
 
`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 1

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0
 

`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0
 
 

`line 14 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0
module spi_helpers_Synchronizer #(
  parameter bit reset_value = 0
) (
  input  logic clk,
  input  logic reset,
  input  logic in_,
  output logic posedge_,
  output logic negedge_,
  output logic out
);
  logic [2:0] shreg;   

`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0
  always_comb begin
    posedge_ = (~shreg[2]) & shreg[1];   
    negedge_ = shreg[2] & (~shreg[1]);   
  end

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0
  always_ff @(posedge clk) begin
    if (reset) begin
      shreg <= {3{reset_value}};
    end else shreg <= {shreg[1:0], in_};
  end

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0
  assign out = shreg[1];

`line 39 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 0
endmodule



`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/synchronizer.v" 2
`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0


`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
module spi_helpers_Minion_PushPull #(
  parameter int nbits = 8
) (
  input  logic             clk,
  input  logic             cs,
  output logic             miso,
  input  logic             mosi,
  input  logic             reset,
  input  logic             sclk,
  output logic             pull_en,
  input  logic [nbits-1:0] pull_msg,
  output logic             push_en,
  output logic [nbits-1:0] push_msg,
  output logic             parity
);
   
   
   

`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  logic cs_sync_clk;
  logic cs_sync_in_;
  logic cs_sync_negedge_;
  logic cs_sync_out;
  logic cs_sync_posedge_;
  logic cs_sync_reset;

`line 41 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  spi_helpers_Synchronizer #(1'b1) cs_sync (
    .clk(cs_sync_clk),
    .in_(cs_sync_in_),
    .negedge_(cs_sync_negedge_),
    .out(cs_sync_out),
    .posedge_(cs_sync_posedge_),
    .reset(cs_sync_reset)
  );

`line 50 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
   
   
   

`line 54 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  logic mosi_sync_clk;
  logic mosi_sync_in_;
  logic mosi_sync_out;
  logic mosi_sync_negedge_;   
  logic mosi_sync_posedge_;   
  logic mosi_sync_reset;

`line 61 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  spi_helpers_Synchronizer #(1'b0) mosi_sync (
    .clk(mosi_sync_clk),
    .in_(mosi_sync_in_),
    .negedge_(mosi_sync_negedge_),
    .out(mosi_sync_out),
    .posedge_(mosi_sync_posedge_),
    .reset(mosi_sync_reset)
  );

`line 70 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
   
   
   

`line 74 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  logic sclk_sync_clk;
  logic sclk_sync_in_;
  logic sclk_sync_negedge_;
  logic sclk_sync_out;   
  logic sclk_sync_posedge_;
  logic sclk_sync_reset;

`line 81 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  spi_helpers_Synchronizer #(1'b0) sclk_sync (
    .clk(sclk_sync_clk),
    .in_(sclk_sync_in_),
    .negedge_(sclk_sync_negedge_),
    .out(sclk_sync_out),
    .posedge_(sclk_sync_posedge_),
    .reset(sclk_sync_reset)
  );

`line 90 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
   
   
   

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  logic             shreg_in_clk;
  logic             shreg_in_in_;
  logic [nbits-1:0] shreg_in_load_data;
  logic             shreg_in_load_en;
  logic [nbits-1:0] shreg_in_out;
  logic             shreg_in_reset;
  logic             shreg_in_shift_en;

`line 102 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  regs_shift_Bitwise #(nbits) shreg_in (
    .clk(shreg_in_clk),
    .reset(shreg_in_reset),
    .d(shreg_in_in_),
    .en(shreg_in_shift_en),
    .load(shreg_in_load_data),
    .load_en(shreg_in_load_en),
    .q(shreg_in_out)
  );

`line 112 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
   
   
   

`line 116 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  logic             shreg_out_clk;
  logic             shreg_out_in_;
  logic [nbits-1:0] shreg_out_load_data;
  logic             shreg_out_load_en;
  logic [nbits-1:0] shreg_out_out;
  logic             shreg_out_reset;
  logic             shreg_out_shift_en;

`line 124 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  regs_shift_Bitwise #(nbits) shreg_out (
    .clk(shreg_out_clk),
    .reset(shreg_out_reset),
    .d(shreg_out_in_),
    .en(shreg_out_shift_en),
    .load(shreg_out_load_data),
    .load_en(shreg_out_load_en),
    .q(shreg_out_out)
  );

`line 134 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  always_comb begin
    shreg_in_shift_en  = (~cs_sync_out) & sclk_sync_posedge_;
    shreg_out_shift_en = (~cs_sync_out) & sclk_sync_negedge_;
  end

`line 139 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
  assign cs_sync_clk         = clk;
  assign cs_sync_reset       = reset;
  assign cs_sync_in_         = cs;
  assign sclk_sync_clk       = clk;
  assign sclk_sync_reset     = reset;
  assign sclk_sync_in_       = sclk;
  assign mosi_sync_clk       = clk;
  assign mosi_sync_reset     = reset;
  assign mosi_sync_in_       = mosi;
  assign shreg_in_clk        = clk;
  assign shreg_in_reset      = reset;
  assign shreg_in_in_        = mosi_sync_out;
  assign shreg_in_load_en    = 1'b0;
  assign shreg_in_load_data  = {nbits{1'b0}};
  assign shreg_out_clk       = clk;
  assign shreg_out_reset     = reset;
  assign shreg_out_in_       = 1'b0;
  assign shreg_out_load_en   = pull_en;
  assign shreg_out_load_data = pull_msg;
  assign miso                = shreg_out_out[nbits-1];
  assign pull_en             = cs_sync_negedge_;
  assign push_en             = cs_sync_posedge_;
  assign push_msg            = shreg_in_out;
  assign parity              = (^push_msg[nbits-3:0]) & push_en;


`line 165 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
   
  logic unused;
  assign unused = &{1'b0, mosi_sync_negedge_, mosi_sync_posedge_, sclk_sync_out, 1'b0};

`line 169 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
endmodule

`line 171 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 0
   

`line 173 "/home/jjm469/c2s2/sp25_tapein1/src/spi/helpers/minion_pushpull.v" 2
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0



`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
 
module spi_Minion #(
  BIT_WIDTH = 32,
  N_SAMPLES = 8
) (
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   cs,
  input  logic                   sclk,
  input  logic                   mosi,
  output logic                   miso,
  input  logic [BIT_WIDTH - 1:0] recv_msg,
  output logic                   recv_rdy,
  input  logic                   recv_val,
  output logic [BIT_WIDTH - 1:0] send_msg,
  input  logic                   send_rdy,
  output logic                   send_val,
  output logic                   minion_parity,
  output logic                   adapter_parity
);

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
  logic                   push_en;
  logic                   pull_en;

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
  logic [BIT_WIDTH + 1:0] push_msg;
  logic [BIT_WIDTH - 1:0] pull_msg;
  logic                   pull_msg_val;
  logic                   pull_msg_spc;

`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
  spi_helpers_Minion_PushPull #(
    .nbits(BIT_WIDTH + 2)
  ) minion (
    .clk(clk),
    .cs(cs),
    .miso(miso),
    .mosi(mosi),
    .reset(reset),
    .sclk(sclk),
    .pull_en(pull_en),
    .pull_msg({pull_msg_val, pull_msg_spc, pull_msg}),
    .push_en(push_en),
    .push_msg(push_msg),
    .parity(minion_parity)
  );

`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
  spi_helpers_Minion_Adapter #(
    .nbits(BIT_WIDTH + 2),
    .num_entries(N_SAMPLES)
  ) adapter1 (
    .clk(clk),
    .reset(reset),
    .pull_en(pull_en),
    .pull_msg_val(pull_msg_val),
    .pull_msg_spc(pull_msg_spc),
    .pull_msg_data(pull_msg),
    .push_en(push_en),
    .push_msg_val_wrt(push_msg[BIT_WIDTH+1]),
    .push_msg_val_rd(push_msg[BIT_WIDTH]),
    .push_msg_data(push_msg[BIT_WIDTH-1:0]),
    .recv_msg(recv_msg),
    .recv_val(recv_val),
    .recv_rdy(recv_rdy),

`line 69 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
    .send_msg(send_msg),
    .send_val(send_val),
    .send_rdy(send_rdy),
    .parity  (adapter_parity)
  );

`line 75 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 0
endmodule

`line 77 "/home/jjm469/c2s2/sp25_tapein1/src/spi/minion.v" 2
`line 14 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
 
 
`line 3 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 
 





`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  
     
 
      
  
                   
     


`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
   
     
         
         
         
    
  







`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  
     
 
      
  
  
              
     


`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
   
     
         
         
         
         
    
  







`line 60 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  
     
 
      
  
  
  
              
     


`line 71 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
   
     
         
         
         
         
         
    
  







`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  
     
 
      
  
  
  
  
              
     


`line 99 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
   
     
         
         
         
         
         
         
    
  







`line 116 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  
     
 
      
  
  
  
  
  
              
     


`line 129 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
   
     
         
         
         
         
         
         
         
    
  







`line 147 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  
     
 
      
  
  
  
  
  
  
              
     


`line 161 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
   
     
         
         
         
         
         
         
         
         
    
  







`line 180 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  
     
 
      
  
  
  
  
  
  
  
              
     


`line 195 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
   
     
         
         
         
         
         
         
         
         
         
    
  







`line 215 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
 

`line 217 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
     
     

`line 220 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
                          
            
                     


`line 225 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
     



`line 229 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 0
  


`line 232 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/muxes.v" 2
`line 3 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
 
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 0
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 0
 
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 0
module cmn_DemuxN
#(
  parameter nbits = 1,   
  parameter noutputs = 2
)(
  input  logic                [nbits-1:0]   in,
  input  logic     [$clog2(noutputs)-1:0]   sel,
  output logic                [nbits-1:0]   out   [0:noutputs-1] 
); 

`line 22 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 0
  genvar i;
  generate
    for (i = 0; i < noutputs; i = i + 1) begin : output_gen
      assign out[i] = (i == sel) ? in : {nbits{1'b0}};
    end
  endgenerate
endmodule

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 0
  
`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/demuxes.v" 2
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
 
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 
 





`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
 
 
 














`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
     
 
    
    

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
       
      

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      
       

`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
             
       
      


`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   

`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
          
  

`line 60 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
         

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
       
       

`line 67 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 69 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
       

`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
       

`line 75 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  

`line 78 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
     

`line 81 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
           

`line 84 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
                

`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
             

`line 89 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  
  

`line 93 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     

`line 95 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  
  
  
  

`line 101 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
                  
                  

`line 104 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 106 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
                      









`line 116 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
          
     
 
                       
                       
                       
                       
      
     


`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 130 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    

`line 132 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
      
    
       
        
        
  

`line 140 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 142 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
       

`line 145 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
         
        
        
        
        
      

`line 152 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
           
         
    
  
















`line 173 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
         
     

`line 177 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
     
 
    
  

`line 183 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
       
      

`line 186 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      
       

`line 189 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
                                
            
             
                          
         


`line 196 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 198 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    
    

`line 201 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
      
    
        
        
  

`line 208 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    
    

`line 211 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
      
    
        
        
  

`line 218 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
      

`line 221 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 223 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
   

`line 226 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
      
    
        
        
  

`line 233 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 235 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
       
       

`line 238 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 240 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
       

`line 243 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
       

`line 246 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  

`line 249 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
         

`line 252 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
           

`line 255 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
           

`line 258 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
       

`line 260 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  
  

`line 264 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     

`line 266 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  
  
  
  

`line 272 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
           
           

`line 275 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 277 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    
       

`line 280 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 282 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    
           

`line 285 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    
       

`line 288 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    
           

`line 291 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 293 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
           

`line 295 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
           

`line 297 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
                 
                                  
                                                           

`line 302 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 304 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   
                      
                     
             
           
                           









`line 319 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
          
     
      

`line 324 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
     
 
                        
                        
                        
      
      
       
      


`line 336 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 338 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    

`line 340 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      
           
     
     
      
    
    
  

`line 349 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 351 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
       

`line 354 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
         
        
        
        
        
      

`line 361 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     
           
         
    
  







`line 373 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
          
     
      

`line 378 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
     
 
    
    

`line 384 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
                       
                      
      

`line 388 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
                      
                       
     

`line 392 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
     


`line 395 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
        

`line 398 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
       
       

`line 401 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
         
                     
                   
                 
                 
                 
                 
                
          
        
      

`line 413 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
          
                   
                 
              
        
               
               
      

`line 422 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
      

`line 424 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
                          
                          
        
        

`line 429 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
          
                     
                   
                 
                 
                 
                 
                
              
               
          
        
      

`line 443 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
           
                   
              
        
            
             
               
               
      

`line 453 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
    
  

`line 456 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 458 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0

`line 467 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0



`line 469 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  

`line 471 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

`line 487 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
  
  



`line 492 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 0
   


`line 495 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/queues.v" 2
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0



`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
 
module arbiter_router_Router #(
  parameter int nbits = 32,
  parameter int noutputs = 8
) (
  input logic clk,
  input logic reset,

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
   
  input  logic             istream_val,
  input  logic [nbits-1:0] istream_msg,
  output logic             istream_rdy,

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
   
  output logic             ostream_val[noutputs],
  output logic [nbits-1:0] ostream_msg[noutputs],
  input  logic             ostream_rdy[noutputs]
);
   
  localparam int n_addr_bits = $clog2(noutputs);

`line 41 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
  logic [n_addr_bits-1:0] select;
  logic [      nbits-1:0] payload_msg;
  logic                   payload_val;
  logic                   payload_rdy;

`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
  assign select = payload_msg[nbits-1 : nbits-n_addr_bits];

`line 48 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
   
  logic [$clog2(3):0] num_free_entries;

`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
  cmn_Queue #(
    .p_msg_nbits(nbits),
    .p_num_msgs (3)
  ) queue_inst (
    .clk             (clk),
    .reset           (reset),
    .enq_val         (istream_val),
    .enq_rdy         (istream_rdy),
    .enq_msg         (istream_msg),
    .deq_val         (payload_val),
    .deq_rdy         (payload_rdy),
    .deq_msg         (payload_msg),
    .num_free_entries(num_free_entries)
  );

`line 66 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
   
  cmn_MuxN #(
    .nbits  (1),
    .ninputs(noutputs)
  ) mux_inst (
    .in (ostream_rdy),
    .sel(select),
    .out(payload_rdy)
  );

`line 76 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
   
  cmn_DemuxN #(
    .nbits   (1),
    .noutputs(noutputs)
  ) demux_inst (
    .in (payload_val),
    .sel(select),
    .out(ostream_val)
  );

`line 86 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
  generate
    for (genvar i = 0; i < noutputs; i = i + 1) begin : output_gen
      assign ostream_msg[i] = payload_msg;
    end
  endgenerate

`line 92 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 0
  /*verilator lint_off UNUSED*/ 
  logic unused = &{1'b0, num_free_entries, 1'b0};
  /*verilator lint_on UNUSED*/ 
endmodule


`line 98 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/router.v" 2
`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
 

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
 

`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
module arbiter_router_Arbiter #(
  parameter int nbits = 32,
  parameter int ninputs = 3,
  localparam int addr_nbits = $clog2(ninputs)
) (
  input logic clk,
  input logic reset,

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
   
  input  logic             istream_val[ninputs],
  output logic             istream_rdy[ninputs],
  input  logic [nbits-1:0] istream_msg[ninputs],

`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
   
  output logic                        ostream_val,
  input  logic                        ostream_rdy,
  output logic [addr_nbits+nbits-1:0] ostream_msg
);
  logic [addr_nbits-1:0] grants_index;   
  logic [addr_nbits-1:0] old_grants_index;
  logic [addr_nbits-1:0] encoder_out;
  logic [     nbits-1:0] ostream_msg_data;
  logic [addr_nbits-1:0] ostream_msg_addr;

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
  assign ostream_msg_data = istream_msg[grants_index];
  assign ostream_msg_addr = grants_index;
  assign ostream_val = istream_val[grants_index] & istream_rdy[grants_index];
  assign ostream_msg = {
    ostream_msg_addr, ostream_msg_data
  };   


`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
  always_comb begin
     
     
    if (!istream_val[old_grants_index]) begin
      grants_index = encoder_out;
    end else begin
      grants_index = old_grants_index;
    end
  end

`line 63 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
  generate
    for (genvar i = 0; i < ninputs; i++) begin : input_assign
       
      assign istream_rdy[i] = (grants_index == i[addr_nbits-1:0]) ? ostream_rdy : 1'b0;
    end
  endgenerate

`line 70 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
  generate
     
     
     
     
    /*verilator lint_off UNOPTFLAT*/ 
    logic [addr_nbits-1:0] encoder_outs[ninputs+1];
    /*verilator lint_on UNOPTFLAT*/ 
    assign encoder_outs[ninputs] = 0;
    for (genvar i = 0; i < ninputs; i++) begin
       
      assign encoder_outs[i] = istream_val[i] ? i : encoder_outs[i+1];
    end
    assign encoder_out = encoder_outs[0];
  endgenerate

`line 86 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
  

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
 

`line 96 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
  always_ff @(posedge clk) begin
    if (reset) begin
      old_grants_index <= 0;
    end else begin
      old_grants_index <= grants_index;
    end
  end

`line 104 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 0
endmodule


`line 107 "/home/jjm469/c2s2/sp25_tapein1/src/arbiter_router/arbiter.v" 2
`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 1

`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
 
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/sine_wave.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/sine_wave.v" 0
 
`default_nettype none

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/sine_wave.v" 0
 
 
module fft_helpers_SineWave #(
  parameter int N = 8,
  parameter int W = 32,
  parameter int D = 16
) (
  output logic [W - 1:0] out[N]
);
   
  localparam real PI = $acos(-1);

`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/sine_wave.v" 0
   
  generate
    if (D >= 32) begin
      $error("D must be less than 32");
    end
    for (genvar i = 0; i < N; i++) begin
      localparam real sinvalue = $sin(2 * PI * i / N);
      /*verilator lint_off UNUSED*/ 
      int fixedptvalue = int'(sinvalue * 2.0 ** D);
       

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/sine_wave.v" 0
      assign out[i] = {{(W - D - 1) {fixedptvalue[31]}}, fixedptvalue[D:0]};
    end
  endgenerate

`line 32 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/sine_wave.v" 0
endmodule



`line 36 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/sine_wave.v" 2
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
 
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/bit_reverse.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/bit_reverse.v" 0
 
`default_nettype none

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/bit_reverse.v" 0
 
 
 
module fft_helpers_BitReverse #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input  logic [BIT_WIDTH - 1:0] in [N_SAMPLES],
  output logic [BIT_WIDTH - 1:0] out[N_SAMPLES]
);
   
  localparam int n = $clog2(N_SAMPLES);

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/bit_reverse.v" 0
  generate
    if (N_SAMPLES == 8) begin
      assign out[0] = in[0];
      assign out[1] = in[4];
      assign out[2] = in[2];
      assign out[3] = in[6];
      assign out[4] = in[1];
      assign out[5] = in[5];
      assign out[6] = in[3];
      assign out[7] = in[7];
    end else begin
      for (genvar m = 0; m < N_SAMPLES; m++) begin
        logic [n-1:0] m_rev;
        for (genvar i = 0; i < n; i++) begin
          assign m_rev[n-i-1] = m[i];
        end
        assign out[m] = in[m_rev];
      end
    end
  endgenerate

`line 39 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/bit_reverse.v" 0
endmodule



`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/fft/helpers/bit_reverse.v" 2
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0

`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
 
`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
 
 
 
 
 
 
 
 
 
 
 
 
 
 
`default_nettype none
 
 
 
`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 1
`default_nettype none
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
 
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 1
`default_nettype none
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 0
module fixed_point_combinational_Multiplier #(
  parameter int n = 32,   
  parameter int d = 16,   
  parameter bit sign = 1   
) (
  input  logic [n-1:0] a,
  input  logic [n-1:0] b,
  output logic [n-1:0] c
);

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 0
  logic [d+n-1:0] prod;
  logic [d+n-1:0] a_ext, b_ext;

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 0
  generate
    if (sign) begin
      assign a_ext = {{d{a[n-1]}}, a};
      assign b_ext = {{d{b[n-1]}}, b};
      assign prod  = (a_ext * b_ext);
    end else begin
      assign prod = (a * b);
    end
  endgenerate

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 0
  assign c = prod[n+d-1:d];


`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 0
   
  generate
    if (d > 0) begin
      /*verilator lint_off UNUSED*/ 
      logic unused;
      /*verilator lint_on UNUSED*/ 
      assign unused = &{1'b0, prod[d-1:0], 1'b0};
    end
  endgenerate

`line 41 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 0
endmodule



`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/multiplier.v" 2
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0


`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
 
module fixed_point_combinational_ComplexMultiplierS #(
  parameter int n = 32,   
  parameter int d = 16    
) (
  input  logic [n-1:0] ar,
  input  logic [n-1:0] ac,
  input  logic [n-1:0] br,
  input  logic [n-1:0] bc,
  output logic [n-1:0] cr,
  output logic [n-1:0] cc
);

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
   
   
  logic [n-1:0] c_ar, c_ac, c_br, c_bc;
  logic [n-1:0] arXbr, acXbc, arcXbrc;

`line 48 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  assign c_ar = ar;
  assign c_ac = ac;
  assign c_br = br;
  assign c_bc = bc;

`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  fixed_point_combinational_Multiplier #(
    .n(n),
    .d(d),
    .sign(1)
  ) arXbrMult (
    .a(c_ar),
    .b(c_br),
    .c(arXbr)
  );

`line 63 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  fixed_point_combinational_Multiplier #(
    .n(n),
    .d(d),
    .sign(1)
  ) acXbcMult (
    .a(c_ac),
    .b(c_bc),
    .c(acXbc)
  );

`line 73 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  fixed_point_combinational_Multiplier #(
    .n(n),
    .d(d),
    .sign(1)
  ) arXbrcMult (
    .a(c_ar + c_ac),
    .b(c_br + c_bc),
    .c(arcXbrc)
  );

`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  assign cr = arXbr - acXbc;
  assign cc = arcXbrc - arXbr - acXbc;

`line 86 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
endmodule

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
 
module fixed_point_combinational_ComplexMultiplier #(
  parameter int n = 32,   
  parameter int d = 16,   
  parameter int num_mults = 1   
) (
  input logic clk,
  input logic reset,
  input logic recv_val,
  output logic recv_rdy,
  output logic send_val,
  input logic send_rdy,
  input logic [n-1:0] ar,
  input logic [n-1:0] ac,
  input logic [n-1:0] br,
  input logic [n-1:0] bc,
  output logic [n-1:0] cr,
  output logic [n-1:0] cc
);
   

`line 142 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
   
   

`line 145 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  logic [n-1:0] c_ar, c_ac, c_br, c_bc;

`line 147 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  logic [n-1:0] arXbr, acXbc, arcXbrc;

`line 149 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
  generate
     
    if (num_mults == 3) begin
      assign c_ar = ar;
      assign c_ac = ac;
      assign c_br = br;
      assign c_bc = bc;

`line 157 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) arXbrMult (
        .a(c_ar),
        .b(c_br),
        .c(arXbr)
      );

`line 167 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) acXbcMult (
        .a(c_ac),
        .b(c_bc),
        .c(acXbc)
      );

`line 177 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) arXbrcMult (
        .a(c_ar + c_ac),
        .b(c_br + c_bc),
        .c(arcXbrc)
      );

`line 187 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      assign cr = arXbr - acXbc;
      assign cc = arcXbrc - arXbr - acXbc;
      assign recv_rdy = send_rdy;
      assign send_val = recv_val;

`line 192 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      logic unused = &({clk, reset});

`line 194 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
       
    end else if (num_mults == 1) begin
       
      logic [2:0] IDLE = 3'd0, MUL1 = 3'd1, MUL2 = 3'd2, MUL3 = 3'd3, DONE = 3'd4;
      logic [2:0] state;
      logic [2:0] next_state;

`line 201 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
       
      logic [n-1:0] mul_a, mul_b, mul_c;

`line 204 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      logic unused = &({IDLE, MUL1, MUL2, MUL3, DONE});

`line 206 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      always_ff @(posedge clk) begin
        if (reset) begin
          state <= IDLE;
          c_ar <= 0;
          c_ac <= 0;
          c_br <= 0;
          c_bc <= 0;
          arXbr <= 0;
          acXbc <= 0;
          arcXbrc <= 0;
        end else begin
          state <= next_state;
          if (state == IDLE && recv_val) begin
             
            c_ar <= ar;
            c_ac <= ac;
            c_br <= br;
            c_bc <= bc;
            arXbr <= 0;
            acXbc <= 0;
            arcXbrc <= 0;
          end else if (state == MUL1) begin
            arXbr <= mul_c;
          end else if (state == MUL2) begin
            acXbc <= mul_c;
          end else if (state == MUL3) begin
            arcXbrc <= mul_c;
          end else begin
          end
        end
      end

`line 238 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      always_comb begin
         
        next_state = state;
        recv_rdy = 0;
        send_val = 0;
        mul_a = 0;
        mul_b = 0;

`line 246 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
        case (state)
          IDLE: begin
            recv_rdy = 1;
            if (recv_val) next_state = MUL1;
            else next_state = IDLE;
          end
          MUL1: begin
            next_state = MUL2;
            mul_a = c_ar;
            mul_b = c_br;
          end
          MUL2: begin
            next_state = MUL3;
            mul_a = c_ac;
            mul_b = c_bc;
          end
          MUL3: begin
            next_state = DONE;
            mul_a = c_ar + c_ac;
            mul_b = c_br + c_bc;
          end
          DONE: begin
            send_val = 1;
            if (send_rdy) next_state = IDLE;
            else next_state = state;
          end
          default: begin
          end
        endcase
      end

`line 277 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      fixed_point_combinational_Multiplier #(
        .n(n),
        .d(d),
        .sign(1)
      ) arXbrMult (
        .a(mul_a),
        .b(mul_b),
        .c(mul_c)
      );

`line 287 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 0
      assign cr = arXbr - acXbc;
      assign cc = arcXbrc - arXbr - acXbc;
    end
  endgenerate
endmodule



`line 295 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/complex_multiplier.v" 2
`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0


`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
module fixed_point_combinational_Butterfly #(
  parameter int n = 32,
  parameter int d = 16,
  parameter int b = 4
   
) (
  input logic [n-1:0] ar[b],
  input logic [n-1:0] ac[b],
  input logic [n-1:0] br[b],
  input logic [n-1:0] bc[b],
  input logic [n-1:0] wr[b],
  input logic [n-1:0] wc[b],

`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
  output logic [n-1:0] cr[b],
  output logic [n-1:0] cc[b],
  output logic [n-1:0] dr[b],
  output logic [n-1:0] dc[b]
);

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
  

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
 

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
  logic [n-1:0] m_cr[b];
  logic [n-1:0] m_cc[b];

`line 48 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
  generate
    for (genvar i = 0; i < b; i++) begin
       
      fixed_point_combinational_ComplexMultiplierS #(
        .n(n),
        .d(d)
      ) mult (
        .ar(wr[i]),
        .ac(wc[i]),
        .br(br[i]),
        .bc(bc[i]),
        .cr(m_cr[i]),
        .cc(m_cc[i])
      );

`line 63 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
      assign cc[i] = ac[i] + m_cc[i];
      assign cr[i] = ar[i] + m_cr[i];
      assign dc[i] = ac[i] - m_cc[i];
      assign dr[i] = ar[i] - m_cr[i];
    end
  endgenerate


`line 71 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 0
endmodule


`line 74 "/home/jjm469/c2s2/sp25_tapein1/src/fixed_point/combinational/butterfly.v" 2
`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
 
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/stride_permutation.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/stride_permutation.v" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/stride_permutation.v" 0
 
 
 
 
module fft_pease_helpers_StridePermutation #(
  parameter int N_SAMPLES = 8,
  parameter int BIT_WIDTH = 32
) (
  input  logic [BIT_WIDTH-1:0] recv[N_SAMPLES],
  output logic [BIT_WIDTH-1:0] send[N_SAMPLES]
);

`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/stride_permutation.v" 0
  generate
    for (genvar i = 0; i < N_SAMPLES / 2; i++) begin
      assign send[i] = recv[i*2];
      assign send[i+N_SAMPLES/2] = recv[i*2+1];
    end
  endgenerate

`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/stride_permutation.v" 0
endmodule



`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/stride_permutation.v" 2
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
 
`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 0
 
module fft_pease_helpers_TwiddleGenerator #(
  parameter int BIT_WIDTH  = 4,
  parameter int DECIMAL_PT = 2,
  parameter int SIZE_FFT   = 8,
  parameter int STAGE_FFT  = 0
) (
  input logic [BIT_WIDTH - 1:0] sine_wave_in[SIZE_FFT],   

`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 0
  output logic [BIT_WIDTH - 1:0] twiddle_real     [SIZE_FFT/2],
  output logic [BIT_WIDTH - 1:0] twiddle_imaginary[SIZE_FFT/2]
);
  generate
    if (STAGE_FFT == 0) begin
      for (genvar i = 0; i < SIZE_FFT / 2; i = i + 1) begin
        assign twiddle_real[i] = {{BIT_WIDTH - DECIMAL_PT - 1{1'b0}}, 1'b1, {DECIMAL_PT{1'b0}}};
        assign twiddle_imaginary[i] = 0;
      end
       
       

`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 0
      logic [(BIT_WIDTH * SIZE_FFT) - 1: 0] packed_sine_wave_in;
      assign packed_sine_wave_in = {<<SIZE_FFT{sine_wave_in}};
      logic unused = &packed_sine_wave_in;

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 0
    end else begin

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 0
      for (genvar m = 0; m < 2 ** STAGE_FFT; m = m + 1) begin
        for (genvar j = 0; j < 2 ** ($clog2(SIZE_FFT) - STAGE_FFT - 1); j = j + 1) begin
          localparam int stageLeft = $clog2(SIZE_FFT) - STAGE_FFT - 1;
          localparam int idx = m * (2 ** stageLeft);
          localparam int si = idx + j;
          assign twiddle_real[si] = sine_wave_in[idx+SIZE_FFT/4];
          assign twiddle_imaginary[si] = sine_wave_in[idx+SIZE_FFT/2];
        end
      end
    end
  endgenerate

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 0
endmodule



`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/helpers/twiddle_generator.v" 2
`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0


`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
module fft_pease_FFT #(
  parameter int BIT_WIDTH  = 32,
  parameter int DECIMAL_PT = 16,
  parameter int N_SAMPLES  = 8
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],
  input  logic                   recv_val,
  output logic                   recv_rdy,

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES],
  output logic                   send_val,
  input  logic                   send_rdy,

`line 24 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  input logic reset,
  input logic clk
);

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  logic [2:0] IDLE = 3'd0, COMP = 3'd1, DONE = 3'd2;

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  localparam int BstageBits = (N_SAMPLES > 2) ? $clog2($clog2(N_SAMPLES)) : 1;
  localparam int log = $clog2(N_SAMPLES) - 1;
  logic [BstageBits-1:0] max_bstage = log[BstageBits-1:0];

`line 34 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  logic [2:0] state;
  logic [2:0] next_state;

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  assign recv_rdy = (state == IDLE || state == DONE);
  assign send_val = (state == DONE);

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  logic [     BstageBits-1:0] bstage;
  logic [     BstageBits-1:0] next_bstage;

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  logic [2 * BIT_WIDTH - 1:0] out_stride   [N_SAMPLES];
  logic [2 * BIT_WIDTH - 1:0] in_butterfly [N_SAMPLES];
  logic [2 * BIT_WIDTH - 1:0] out_butterfly[N_SAMPLES];

`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  logic [    BIT_WIDTH - 1:0] reversed_msg [N_SAMPLES];
  fft_helpers_BitReverse #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH)
  ) bit_reverse (
    .in (recv_msg),
    .out(reversed_msg)
  );

`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  fft_pease_helpers_StridePermutation #(
    .N_SAMPLES(N_SAMPLES),
    .BIT_WIDTH(BIT_WIDTH * 2)
  ) stride_permutation (
    .recv(out_butterfly),
    .send(out_stride)
  );

`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  logic [BIT_WIDTH - 1:0] sine_wave_out[        N_SAMPLES];
  logic [BIT_WIDTH - 1:0] wr           [$clog2(N_SAMPLES)] [N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] wc           [$clog2(N_SAMPLES)] [N_SAMPLES/2];

`line 68 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  generate
    for (genvar i = 0; i < $clog2(N_SAMPLES); i++) begin
      fft_pease_helpers_TwiddleGenerator #(
        .BIT_WIDTH (BIT_WIDTH),
        .DECIMAL_PT(DECIMAL_PT),
        .SIZE_FFT  (N_SAMPLES),
        .STAGE_FFT (i)
      ) twiddle_generator (
        .sine_wave_in(sine_wave_out),
        .twiddle_real(wr[i]),
        .twiddle_imaginary(wc[i])
      );
    end
  endgenerate

`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  fft_helpers_SineWave #(
    .N(N_SAMPLES),
    .W(BIT_WIDTH),
    .D(DECIMAL_PT)
  ) sine_wave (
    .out(sine_wave_out)
  );


`line 92 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  logic [BIT_WIDTH - 1:0] ar[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] ac[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] br[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] bc[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] cr[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] cc[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] dr[N_SAMPLES/2];
  logic [BIT_WIDTH - 1:0] dc[N_SAMPLES/2];

`line 101 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  generate
    for (genvar i = 0; i < N_SAMPLES / 2; i++) begin
      assign ar[i] = in_butterfly[i*2][BIT_WIDTH-1:0];
      assign ac[i] = in_butterfly[i*2][2*BIT_WIDTH-1:BIT_WIDTH];
      assign br[i] = in_butterfly[i*2+1][BIT_WIDTH-1:0];
      assign bc[i] = in_butterfly[i*2+1][2*BIT_WIDTH-1:BIT_WIDTH];
      assign out_butterfly[i*2][BIT_WIDTH-1:0] = cr[i];
      assign out_butterfly[i*2][2*BIT_WIDTH-1:BIT_WIDTH] = cc[i];
      assign out_butterfly[i*2+1][BIT_WIDTH-1:0] = dr[i];
      assign out_butterfly[i*2+1][2*BIT_WIDTH-1:BIT_WIDTH] = dc[i];
    end
  endgenerate

`line 114 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin
      assign send_msg[i] = in_butterfly[i][BIT_WIDTH-1:0];
    end
  endgenerate

`line 120 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  fixed_point_combinational_Butterfly #(
    .n(BIT_WIDTH),
    .d(DECIMAL_PT),
    .b(N_SAMPLES / 2)
  ) fft_stage (
    .wr(wr[bstage]),
    .wc(wc[bstage]),
    .*
  );

`line 130 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  always_comb begin
    next_state  = state;
    next_bstage = bstage;
    if (state == IDLE && recv_val) begin
      next_state = COMP;
    end else begin
      if (state == COMP) begin
        if (bstage == max_bstage) begin
          next_state  = DONE;
          next_bstage = 0;
        end else begin
          next_bstage = bstage + 1;
        end
      end else begin
        if (state == DONE && send_rdy) begin
          if (recv_val) begin
            next_state = COMP;
          end else begin
            next_state = IDLE;
          end
        end else begin
        end
      end
    end
  end

`line 156 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  always_ff @(posedge clk) begin
    if (reset) begin
      state  <= IDLE;
      bstage <= 0;
    end else begin
      state  <= next_state;
      bstage <= next_bstage;
    end
  end

`line 166 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin
      always_ff @(posedge clk) begin
        if (reset) begin
          in_butterfly[i] <= 0;
        end else begin
          if (state == IDLE || state == DONE && recv_val) begin
            in_butterfly[i][BIT_WIDTH-1:0] <= reversed_msg[i];
            in_butterfly[i][2*BIT_WIDTH-1:BIT_WIDTH] <= 0;
          end else begin
            if (state == COMP) begin
              in_butterfly[i] <= out_stride[i];
            end else begin
            end
          end
        end
      end
    end
  endgenerate

`line 186 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 0
endmodule



`line 190 "/home/jjm469/c2s2/sp25_tapein1/src/fft/pease/fft.v" 2
`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 1
`default_nettype none
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
 
 
 
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 





`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
           


`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
       







`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
             


`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
           







`line 55 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
          
                       


`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
         







`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
            
                         


`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
               



`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
   


`line 90 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 2
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0


`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
module serdes_Deserializer #(
  parameter int N_SAMPLES = 8,
  parameter int BIT_WIDTH = 32
) (

`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  input logic recv_val,
  output logic recv_rdy,
  input logic [BIT_WIDTH - 1:0] recv_msg,

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  output logic send_val,
  input logic send_rdy,
  output logic [BIT_WIDTH - 1:0] send_msg[N_SAMPLES],

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  input logic clk,
  input logic reset
);

`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  generate
    if (N_SAMPLES == 1) begin
      assign recv_rdy = send_rdy;
      assign send_val = recv_val;
      assign send_msg[0] = recv_msg;

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
      logic unused = {1'b0, clk, reset, 1'b0};
    end else begin
      logic [N_SAMPLES - 1:0] en_sel;

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
       
      DeserializerControl #(
        .N_SAMPLES(N_SAMPLES)
      ) c (
        .recv_val(recv_val),
        .send_rdy(send_rdy),

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
        .send_val(send_val),
        .recv_rdy(recv_rdy),

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
        .reset(reset),
        .clk  (clk),

`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
        .en_sel(en_sel)
      );

`line 49 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
      for (genvar i = 0; i < N_SAMPLES; i++) begin : l_regs
        cmn_EnResetReg #(BIT_WIDTH) register (
          .clk(clk),
          .reset(reset),
          .en(recv_rdy & en_sel[i]),
          .d(recv_msg),
          .q(send_msg[i])
        );
      end
    end
  endgenerate

`line 61 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
endmodule

`line 63 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
module DeserializerControl #(
  parameter int N_SAMPLES = 8
) (
  input logic recv_val,
  input logic send_rdy,

`line 69 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  output logic send_val,
  output logic recv_rdy,

`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  output logic [N_SAMPLES - 1:0] en_sel,

`line 74 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  input logic reset,
  input logic clk
);
  logic INIT = 1'b0, DONE = 1'b1;

`line 79 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  localparam int C_WIDTH = $clog2(N_SAMPLES) - 1;
   
   
  localparam int C_NXT_WIDTH = $clog2(N_SAMPLES + 1) - 1;
  logic [C_WIDTH:0] count;   
  logic [C_NXT_WIDTH:0] count_next;

`line 86 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  logic next_state;
  logic state;

`line 89 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  Decoder #($clog2(
      N_SAMPLES
  )) decoder (
    .in (count),
    .out(en_sel)
  );

`line 96 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  always_comb begin
    case (state)
      INIT: begin
        if (count_next == N_SAMPLES[C_NXT_WIDTH:0]) begin
          next_state = DONE;
        end else begin
          next_state = INIT;
        end
      end
      DONE: begin
        if (send_rdy == 1) begin
          next_state = INIT;
        end else begin
          next_state = DONE;
        end
      end
      default: next_state = INIT;
    endcase
  end

`line 116 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  always_comb begin
    case (state)
      INIT: begin
        if (recv_val == 1) begin
          count_next = {{(C_NXT_WIDTH - C_WIDTH) {1'b0}}, count} + 1;
        end else begin
          count_next = {{(C_NXT_WIDTH - C_WIDTH) {1'b0}}, count};
        end

`line 125 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
        recv_rdy = 1'b1;
        send_val = 1'b0;
      end

`line 129 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
      DONE: begin
        count_next = 0;
        recv_rdy   = 1'b0;
        send_val   = 1'b1;
      end

`line 135 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
      default: begin
        count_next = 0;
        recv_rdy   = 1'b1;
        send_val   = 1'b0;
      end

`line 141 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
    endcase

`line 143 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  end

`line 145 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
  always_ff @(posedge clk) begin
    if (reset) begin
      count <= 0;
      state <= INIT;
    end else begin
      count <= count_next[$clog2(N_SAMPLES)-1:0];
      state <= next_state;
    end
  end
endmodule

`line 156 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 0
module Decoder #(
  parameter int BIT_WIDTH = 3
) (
  input logic [BIT_WIDTH - 1:0] in,
  output logic [(1 << BIT_WIDTH) - 1:0] out
);
  assign out = {{(1 << BIT_WIDTH) - 1{1'b0}}, 1'b1} << in;
endmodule


`line 166 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/deserializer.v" 2
`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 1
`default_nettype none
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
 
 
 
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 





`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
           


`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
       







`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
             


`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
           







`line 55 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
          
                       


`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
         







`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
            
                         


`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
               



`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
   


`line 90 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 2
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0


`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
module serdes_Serializer #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],
  input logic recv_val,
  output logic recv_rdy,

`line 14 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  output logic [BIT_WIDTH - 1:0] send_msg,
  output logic send_val,
  input logic send_rdy,

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  input logic reset,
  input logic clk
);
  generate
    if (N_SAMPLES == 1) begin
      assign recv_rdy = send_rdy;
      assign send_val = recv_val;
      assign send_msg = recv_msg[0];

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
      logic unused = {1'b0, clk, reset, 1'b0};
    end else begin
      logic [$clog2(N_SAMPLES) - 1:0] mux_sel;
      logic reg_en;
      logic [BIT_WIDTH - 1:0] reg_out[N_SAMPLES - 1:0];

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
      for (genvar i = 0; i < N_SAMPLES; i++) begin : l_regs
        cmn_EnResetReg #(BIT_WIDTH) register (
          .clk(clk),
          .reset(reset),
          .en(reg_en),
          .d(recv_msg[i]),
          .q(reg_out[i])
        );
      end

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
      assign send_msg = reg_out[mux_sel];

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
      SerializerControl #(
        .N_SAMPLES(N_SAMPLES)
      ) ctrl (
        .clk(clk),
        .reset(reset),
        .recv_val(recv_val),
        .recv_rdy(recv_rdy),
        .send_val(send_val),
        .send_rdy(send_rdy),
        .mux_sel(mux_sel),
        .reg_en(reg_en)
      );
    end
  endgenerate
endmodule


`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
module SerializerControl #(
  parameter int N_SAMPLES = 8
) (
  input  logic recv_val,
  output logic recv_rdy,

`line 68 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  output logic send_val,
  input  logic send_rdy,

`line 71 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  output logic [$clog2(N_SAMPLES) - 1:0] mux_sel,
  output logic reg_en,

`line 74 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  input logic clk,
  input logic reset
);

`line 78 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  logic INIT = 1'b0, OUTPUT_START = 1'b1;

`line 80 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  logic next_state;
  logic state;

`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
   
  localparam int NS_EXC_W = $clog2(N_SAMPLES);
   
  localparam int NS_W = $clog2(N_SAMPLES + 1);
  logic [NS_W-1:0] mux_sel_next;

`line 89 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  always_comb begin
    case (state)
      INIT: begin
        if (reset == 1) next_state = INIT;
        else if (recv_val == 1) next_state = OUTPUT_START;
        else next_state = INIT;
      end
      OUTPUT_START: begin
        if (mux_sel_next != N_SAMPLES[NS_W-1:0]) next_state = OUTPUT_START;
        else next_state = INIT;
      end
      default: next_state = INIT;
    endcase
  end

`line 104 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  always_comb begin
    case (state)
      INIT: begin
        reg_en = 1;
        send_val = 0;
        recv_rdy = 1;
        mux_sel_next = 0;
      end
      OUTPUT_START: begin
        reg_en   = 0;
        send_val = 1;
        recv_rdy = 0;
        if (send_rdy == 1) mux_sel_next = {{(NS_W - NS_EXC_W) {1'b0}}, mux_sel} + 1;
        else mux_sel_next = {{(NS_W - NS_EXC_W) {1'b0}}, mux_sel};
      end
      default: begin
        reg_en = 1;
        send_val = 0;
        recv_rdy = 1;
        mux_sel_next = 0;
      end
    endcase
  end

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 0
  always_ff @(posedge clk) begin
    if (reset) begin
      state   <= INIT;
      mux_sel <= 0;
    end else begin
      mux_sel <= mux_sel_next[NS_EXC_W-1:0];
      state   <= next_state;
    end
  end
endmodule


`line 140 "/home/jjm469/c2s2/sp25_tapein1/src/serdes/serializer.v" 2
`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
 

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
module crossbars_Blocking #(
  parameter int BIT_WIDTH = 32,
  parameter int N_INPUTS = 2,
  parameter int N_OUTPUTS = 2,
  localparam int CONTROL_BIT_WIDTH = $clog2(N_INPUTS * N_OUTPUTS)
) (
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_INPUTS],
  input  logic                   recv_val[N_INPUTS],
  output logic                   recv_rdy[N_INPUTS],

`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  output logic [BIT_WIDTH - 1:0] send_msg[N_OUTPUTS],
  output logic                   send_val[N_OUTPUTS],
  input  logic                   send_rdy[N_OUTPUTS],

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  input logic reset,
  input logic clk,

`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  input  logic [CONTROL_BIT_WIDTH - 1:0] control,
  input  logic                           control_val,
  output logic                           control_rdy
);

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  logic [CONTROL_BIT_WIDTH - 1:0] stored_control;
  logic [$clog2(N_INPUTS)  - 1:0] input_sel;
  logic [$clog2(N_OUTPUTS) - 1:0] output_sel;

`line 32 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  always_ff @(posedge clk) begin
    if (reset) begin
      stored_control <= 0;
    end else if (control_val) begin
      stored_control <= control;
    end else begin
      stored_control <= stored_control;
    end
  end

`line 42 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  assign control_rdy = 1;



`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  assign input_sel = stored_control[CONTROL_BIT_WIDTH-1:CONTROL_BIT_WIDTH-$clog2(N_INPUTS)];

`line 48 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  assign output_sel = stored_control[CONTROL_BIT_WIDTH-$clog2(
      N_INPUTS
  )-1 : CONTROL_BIT_WIDTH-$clog2(
      N_INPUTS
  )-$clog2(
      N_OUTPUTS
  )];

`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
  always_comb begin
    for (int i = 0; i < N_OUTPUTS; i = i + 1) begin
      /*verilator lint_off WIDTH*/ 
      if ((i != output_sel)) begin
        /*verilator lint_on WIDTH*/ 
        send_msg[i] = 0;
        send_val[i] = 0;
      end else begin
        send_msg[i] = recv_msg[input_sel];
        send_val[i] = recv_val[input_sel];
      end
    end
    for (int i = 0; i < N_INPUTS; i = i + 1) begin
      /*verilator lint_off WIDTH*/ 
      if ((i != input_sel)) begin
        /*verilator lint_on WIDTH*/ 
        recv_rdy[i] = 0;
      end else begin
        recv_rdy[i] = send_rdy[output_sel];
      end
    end
  end

`line 79 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 0
endmodule



`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/crossbars/blocking.v" 2
`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
 
 
`default_nettype none
 
 
 
`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 





`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
           


`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
       







`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
             


`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
           







`line 55 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
          
                       


`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
         







`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
            
                         


`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
               



`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
   


`line 90 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 2
`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
 
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/magnitude.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/magnitude.v" 0
 
 
`default_nettype none
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/magnitude.v" 0
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

`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/magnitude.v" 0
endmodule



`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/magnitude.v" 2
`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
 
`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/highpass.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/highpass.v" 0
 
 
`default_nettype none
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/highpass.v" 0
module highpass_Highpass #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input  logic [BIT_WIDTH - 1:0] cutoff_freq,
  input  logic [BIT_WIDTH - 1:0] freq_in       [N_SAMPLES],
  output logic                   filtered_valid[N_SAMPLES]
);

`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/highpass.v" 0
  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
      assign filtered_valid[i] = freq_in[i] > cutoff_freq;
    end
  endgenerate


`line 24 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/highpass.v" 0
endmodule



`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/highpass.v" 2
`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0

`line 10 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
 
`line 10 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
 
 
`default_nettype none
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
 
 
module classifier_helpers_FrequencyBins #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 16
) (
  input  logic [BIT_WIDTH - 1:0] sampling_freq,
  output logic [BIT_WIDTH - 1:0] frequency_out[N_SAMPLES]
);

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
  localparam int LOG2_N_SAMPLES = $clog2(N_SAMPLES);

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
  initial begin
    if ($pow(2, LOG2_N_SAMPLES) != N_SAMPLES) begin
      $error("N_SAMPLES must be a power of 2");
    end
  end

`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
   
  wire [LOG2_N_SAMPLES + BIT_WIDTH - 1:0] wide_sampling_freq = {
    (LOG2_N_SAMPLES)'(0), sampling_freq
  };

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
  generate
    for (genvar i = 0; i < N_SAMPLES; i++) begin : gen_freq
      wire [LOG2_N_SAMPLES + BIT_WIDTH - 1:0] wide_freq_out = (i * wide_sampling_freq) >> (LOG2_N_SAMPLES + 1);
      assign frequency_out[i] = wide_freq_out[BIT_WIDTH-1:0];

`line 36 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
      wire unused = &{1'b0, wide_freq_out[LOG2_N_SAMPLES+BIT_WIDTH-1:BIT_WIDTH], 1'b0};
    end
  endgenerate

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 0
endmodule



`line 44 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/frequency_bins.v" 2
`line 10 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0

`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
 
`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/comparison.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/comparison.v" 0
 
 
`default_nettype none
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/comparison.v" 0
module comparison_Comparison #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input  logic [BIT_WIDTH - 1:0] cutoff_mag,
  input  logic                   filtered_valid[N_SAMPLES],
  input  logic [BIT_WIDTH - 1:0] mag_in        [N_SAMPLES],
  output logic                   compare_out
);
  logic [N_SAMPLES-1:0] compare_outs;

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/comparison.v" 0
  generate
    for (genvar i = 0; i < N_SAMPLES; i = i + 1) begin
      assign compare_outs[i] = filtered_valid[i] & (mag_in[i] > cutoff_mag);
    end
  endgenerate

`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/comparison.v" 0
  assign compare_out = compare_outs != 0;
endmodule



`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/helpers/comparison.v" 2
`line 11 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0


`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
module classifier_Classifier #(
  parameter int BIT_WIDTH = 32,
  parameter int DECIMAL_PT = 16,
   
   
  parameter int FREQ_BIT_WIDTH = 16,
  parameter int N_SAMPLES = 8
) (
  input logic clk,
  input logic reset,

`line 24 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  output logic                   recv_rdy,
  input  logic                   recv_val,
  input  logic [BIT_WIDTH - 1:0] recv_msg[N_SAMPLES],

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  output logic                        cutoff_freq_rdy,
  input  logic                        cutoff_freq_val,
  input  logic [FREQ_BIT_WIDTH - 1:0] cutoff_freq_msg,

`line 32 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  output logic                   cutoff_mag_rdy,
  input  logic                   cutoff_mag_val,
  input  logic [BIT_WIDTH - 1:0] cutoff_mag_msg,

`line 36 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  output logic                        sampling_freq_rdy,
  input  logic                        sampling_freq_val,
  input  logic [FREQ_BIT_WIDTH - 1:0] sampling_freq_msg,

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  input  logic send_rdy,
  output logic send_val,
  output logic send_msg
);

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  logic [FREQ_BIT_WIDTH-1:0] in_cutoff_freq;
  logic [BIT_WIDTH-1:0] in_cutoff_mag;
  logic [FREQ_BIT_WIDTH-1:0] in_sampling_freq;

`line 49 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  cmn_EnResetReg #(
    .p_nbits      (FREQ_BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_freq_in (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_freq_msg),
    .q    (in_cutoff_freq),
    .en   (cutoff_freq_val)
  );
  assign cutoff_freq_rdy = 1;

`line 61 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  cmn_EnResetReg #(
    .p_nbits      (BIT_WIDTH),
    .p_reset_value(0)
  ) cutoff_mag_in (
    .clk  (clk),
    .reset(reset),
    .d    (cutoff_mag_msg),
    .q    (in_cutoff_mag),
    .en   (cutoff_mag_val)
  );
  assign cutoff_mag_rdy = 1;

`line 73 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  cmn_EnResetReg #(
    .p_nbits      (FREQ_BIT_WIDTH),
    .p_reset_value(0)
  ) sampling_freq_in (
    .clk  (clk),
    .reset(reset),
    .d    (sampling_freq_msg),
    .q    (in_sampling_freq),
    .en   (sampling_freq_val)
  );
  assign sampling_freq_rdy = 1;

`line 85 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
   
  logic [BIT_WIDTH-1:0] out_mag[N_SAMPLES];

`line 88 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  magnitude_Magnitude #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) mag_calc (
    .recv_msg(recv_msg),
    .send_msg(out_mag)
  );

`line 96 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
   
  logic [FREQ_BIT_WIDTH-1:0] frequency_array[N_SAMPLES];

`line 99 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  classifier_helpers_FrequencyBins #(
    .BIT_WIDTH(FREQ_BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) freq_gen (
    .sampling_freq(in_sampling_freq),
    .frequency_out(frequency_array)
  );

`line 107 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  logic out_filter[N_SAMPLES];

`line 109 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  highpass_Highpass #(
    .BIT_WIDTH(FREQ_BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) highpass_fil (
    .cutoff_freq(in_cutoff_freq),
    .freq_in(frequency_array),
    .filtered_valid(out_filter)
  );

`line 118 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
   
  logic out_comparison;

`line 121 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  comparison_Comparison #(
    .BIT_WIDTH(BIT_WIDTH),
    .N_SAMPLES(N_SAMPLES)
  ) comparison (
    .cutoff_mag(in_cutoff_mag),
    .filtered_valid(out_filter),
    .mag_in(out_mag),
    .compare_out(out_comparison)
  );

`line 131 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 0
  assign send_msg = out_comparison;
  assign send_val = recv_val;
  assign recv_rdy = send_rdy;
endmodule



`line 138 "/home/jjm469/c2s2/sp25_tapein1/src/classifier/classifier.v" 2
`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 22 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 22 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
 
 
 
 
 

`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
 
 
 
 
 
 
 
 
 

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

`line 41 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
 
 

`line 44 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
module lbist_controller #(
    parameter int SEED_BITS = 32,             
    parameter int SIGNATURE_BITS = 32,        
    parameter int NUM_SEEDS = 8,              
    parameter int NUM_HASHES = 8,             
    parameter int MAX_OUTPUTS_TO_HASH = 32,   
    parameter int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH),
    parameter [SEED_BITS-1:0] LFSR_SEEDS [NUM_SEEDS-1:0] = {
      32'h0a89687e,
      32'ha87ded5f,
      32'h481c5077,
      32'h81595729,
      32'hffd39769,
      32'h24b05d57,
      32'h9913b1fd,
      32'hd8df8ed2
    },
    parameter [SIGNATURE_BITS-1:0] EXPECTED_SIGNATURES [NUM_SEEDS-1:0] = {
      32'h2435b217,
      32'hb25e4d4c,
      32'h16307bd1,
      32'h2ced25e0,
      32'hc5145ccb,
      32'h6180254b,
      32'hc329c75c,
      32'h89b9c2ec
    }
    )(
    input logic clk,
    input logic reset,

`line 75 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
     
    input  logic                      lbist_req_val,
    output logic                      lbist_req_rdy,

`line 79 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
     
    output logic                      lbist_resp_val,
    output logic [NUM_SEEDS-1:0]      lbist_resp_msg,
    input  logic                      lbist_resp_rdy,

`line 84 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
     
    output logic                      lfsr_resp_val,
    output logic [SEED_BITS-1:0]      lfsr_resp_msg,
    input  logic                      lfsr_resp_rdy,

`line 89 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
     
    output logic                      misr_req_val,
    output logic [MISR_MSG_BITS:0]    misr_req_msg,
    input  logic                      misr_req_rdy,

`line 94 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
     
    input  logic                      misr_resp_val,
    input  logic [SIGNATURE_BITS-1:0] misr_resp_msg,
    output logic                      misr_resp_rdy,

`line 99 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
     
    output logic                      lfsr_cut_reset
  );

`line 103 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
 

`line 105 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
  localparam [1:0] IDLE = 2'd0;
  localparam [1:0] START = 2'd1;
  localparam [1:0] COMP_SIG = 2'd2;
  logic [1:0] state;
  logic [1:0] next_state;
  logic [$clog2(NUM_SEEDS)-1:0] counter;

`line 112 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
 

`line 114 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
  always_comb begin
    case (state)
      IDLE: begin
        lbist_req_rdy  = 1;                   
        lfsr_resp_val  = 0;
        lfsr_resp_msg  = 0;
        misr_req_val   = 0;
        misr_req_msg   = 0;
        misr_resp_rdy  = 0;
        lfsr_cut_reset = 0;
      end
      START: begin
        lbist_req_rdy  = 0;
        lfsr_resp_val  = 1;                    
        lfsr_resp_msg  = LFSR_SEEDS[counter];  
        misr_req_val   = 1;                    
        misr_req_msg   = NUM_HASHES;           
        misr_resp_rdy  = 0;
        lfsr_cut_reset = 0;
      end
      COMP_SIG: begin
        lbist_req_rdy  = 0;
        lfsr_resp_val  = 0;
        lfsr_resp_msg  = 0;
        misr_req_val   = 0;
        misr_req_msg   = 0;
        misr_resp_rdy  = 1;                    
        lfsr_cut_reset = 1;                    
      end

`line 144 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
       
      default: begin
        lbist_req_rdy  = 1;
        lfsr_resp_val  = 0;
        lfsr_resp_msg  = 0;
        misr_req_val   = 0;
        misr_req_msg   = 0;
        misr_resp_rdy  = 0;
        lfsr_cut_reset = 0;
      end
    endcase
  end

`line 157 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
 

`line 159 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
  always_comb begin
    case (state)
      IDLE: begin
        if (lbist_req_val && lfsr_resp_rdy && misr_req_rdy) next_state = START;
        else next_state = IDLE;
      end
      START: begin
        if (misr_resp_val) next_state = COMP_SIG;
        else next_state = START;
      end
      COMP_SIG: begin
        if (counter != NUM_SEEDS - 1) next_state = START;
        else if (lbist_resp_rdy && lbist_resp_val) next_state = IDLE;
        else next_state = COMP_SIG;
      end
      default: begin
        next_state = IDLE;
      end
    endcase
  end

`line 180 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
   
  always_ff @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

`line 189 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
   
  always_ff @(posedge clk) begin
    if (reset || state == IDLE) begin
      counter <= 0;
    end else if (state == COMP_SIG && next_state == START) begin
      counter <= counter + 1;
    end else begin
      counter <= counter;
    end
  end

`line 200 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
   
  always_ff @(posedge clk) begin
    case (state)
      IDLE: begin
        lbist_resp_val <= 0;
        lbist_resp_msg <= '0;
      end
      START: begin
        lbist_resp_val <= 0;
        lbist_resp_msg <= lbist_resp_msg;
      end
      COMP_SIG: begin
        lbist_resp_val <= counter == (NUM_SEEDS - 1);
        for (int i = 0; i < NUM_SEEDS; i++) begin
          if (i == counter && misr_resp_val) begin
             
            lbist_resp_msg[i] <= misr_resp_msg == EXPECTED_SIGNATURES[i];
          end else begin
            lbist_resp_msg[i] <= lbist_resp_msg[i];
          end
        end
      end

`line 223 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
       
      default: begin
        lbist_resp_val <= 0;
        lbist_resp_msg <= '0;
      end
    endcase
  end

`line 231 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 0
endmodule
  

`line 234 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lbist_controller/lbist_controller.v" 2
`line 22 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
 
 
 

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
 
 
 
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
 
 

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
 
 
 
 
 
 
 
 
 
 

`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
module lfsr_galois#(
    parameter LFSR_MSG_BITS = 64
)
(
    input logic clk,
    input logic reset,

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
    input logic [LFSR_MSG_BITS-1:0] req_msg,
    input logic req_val,
    output logic req_rdy,

`line 38 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
    input logic resp_rdy,
    output logic resp_val,
    output logic [LFSR_MSG_BITS-1:0] resp_msg

`line 43 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
);


`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
 
     
     
     
    logic [1:0] IDLE = 2'b00;
    logic [1:0] GEN_VAL = 2'b01;

`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
    logic [1:0] state;
    logic [1:0] next_state;

`line 57 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
    logic tap1;
    logic tap2;
    logic final_tap;

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
    logic [LFSR_MSG_BITS-1:0] Q;
    logic [LFSR_MSG_BITS-1:0] next_Q;

`line 66 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
      
     
    int T1;
    int T2;
    int T3;
    int T4;
    localparam int NUM_TAPS = (LFSR_MSG_BITS == 8 || 
                            LFSR_MSG_BITS == 12 || 
                            LFSR_MSG_BITS == 13 || 
                            LFSR_MSG_BITS == 14 || 
                            LFSR_MSG_BITS == 16 || 
                            LFSR_MSG_BITS == 19 || 
                            LFSR_MSG_BITS == 24 || 
                            LFSR_MSG_BITS == 26 || 
                            LFSR_MSG_BITS == 27 || 
                            LFSR_MSG_BITS == 30 || 
                            LFSR_MSG_BITS == 32 ||
                            LFSR_MSG_BITS == 34 || 
                            LFSR_MSG_BITS == 37 || 
                            LFSR_MSG_BITS == 38 || 
                            LFSR_MSG_BITS == 40 || 
                            LFSR_MSG_BITS == 42 ||
                            LFSR_MSG_BITS == 43 ||
                            LFSR_MSG_BITS == 44 ||
                            LFSR_MSG_BITS == 45 ||
                            LFSR_MSG_BITS == 46 ||
                            LFSR_MSG_BITS == 48 ||
                            LFSR_MSG_BITS == 50 ||
                            LFSR_MSG_BITS == 51 ||
                            LFSR_MSG_BITS == 53 ||
                            LFSR_MSG_BITS == 54 ||
                            LFSR_MSG_BITS == 56 ||
                            LFSR_MSG_BITS == 59 ||
                            LFSR_MSG_BITS == 61 ||
                            LFSR_MSG_BITS == 62 ||
                            LFSR_MSG_BITS == 64 ) ? 1 : 0;  

`line 103 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
    generate
         if (LFSR_MSG_BITS == 2) begin
            assign T1 = 0;
            assign T2 = 1;
        end
        else if (LFSR_MSG_BITS == 3) begin
            assign T1 = 1;
            assign T2 = 2;
        end
        else if (LFSR_MSG_BITS == 4) begin
            assign T1 = 2;
            assign T2 = 3;
        end
        else if (LFSR_MSG_BITS == 5) begin
            assign T1 = 2;
            assign T2 = 4;
        end
        else if (LFSR_MSG_BITS == 6) begin
            assign T1 = 4;
            assign T2 = 5;
        end
        else if (LFSR_MSG_BITS == 7) begin
            assign T1 = 5;
            assign T2 = 6;
        end
        else if (LFSR_MSG_BITS == 8) begin
            assign T1 = 3;
            assign T2 = 4;
            assign T3 = 5;
            assign T4 = 7;
        end
        else if (LFSR_MSG_BITS == 9) begin
            assign T1 = 4;
            assign T2 = 8;
        end
        else if (LFSR_MSG_BITS == 10) begin
            assign T1 = 6;
            assign T2 = 9;
        end
        else if (LFSR_MSG_BITS == 11) begin
            assign T1 = 8;
            assign T2 = 10;
        end
        else if (LFSR_MSG_BITS == 12) begin
            assign T1 = 5;
            assign T2 = 7;
            assign T3 = 10;
            assign T4 = 11;
        end
        else if (LFSR_MSG_BITS == 13) begin
            assign T1 = 8;
            assign T2 = 9;
            assign T3 = 11;
            assign T4 = 12;
        end
        else if (LFSR_MSG_BITS == 14) begin
            assign T1 = 8;
            assign T2 = 10;
            assign T3 = 12;
            assign T4 = 13;
        end
        else if (LFSR_MSG_BITS == 15) begin
            assign T1 = 13;
            assign T2 = 14;
        end
        else if (LFSR_MSG_BITS == 16) begin
            assign T1 = 10;
            assign T2 = 12;
            assign T3 = 13;
            assign T4 = 15;
        end
        else if (LFSR_MSG_BITS == 17) begin
            assign T1 = 13;
            assign T2 = 16;
        end
        else if (LFSR_MSG_BITS == 18) begin
            assign T1 = 10;
            assign T2 = 17;
        end
        else if (LFSR_MSG_BITS == 19) begin
            assign T1 = 13;
            assign T2 = 16;
            assign T3 = 17;
            assign T4 = 18;
        end
        else if (LFSR_MSG_BITS == 20) begin
            assign T1 = 16;
            assign T2 = 19;
        end
        else if (LFSR_MSG_BITS == 21) begin
            assign T1 = 18;
            assign T2 = 20;
        end
        else if (LFSR_MSG_BITS == 22) begin
            assign T1 = 20;
            assign T2 = 21;
        end
        else if (LFSR_MSG_BITS == 23) begin
            assign T1 = 17;
            assign T2 = 22;
        end
        else if (LFSR_MSG_BITS == 24) begin
            assign T1 = 19;
            assign T2 = 20;
            assign T3 = 22;
            assign T4 = 23;
        end
        else if (LFSR_MSG_BITS == 25) begin
            assign T1 = 21;
            assign T2 = 24;
        end
        else if (LFSR_MSG_BITS == 26) begin
            assign T1 = 19;
            assign T2 = 20;
            assign T3 = 24;
            assign T4 = 25;
        end
        else if (LFSR_MSG_BITS == 27) begin
            assign T1 = 21;
            assign T2 = 22;
            assign T3 = 24;
            assign T4 = 26;
        end
        else if (LFSR_MSG_BITS == 28) begin
            assign T1 = 24;
            assign T2 = 27;
        end
        else if (LFSR_MSG_BITS == 29) begin
            assign T1 = 26;
            assign T2 = 28;
        end
        else if (LFSR_MSG_BITS == 30) begin
            assign T1 = 23;
            assign T2 = 25;
            assign T3 = 27;
            assign T4 = 29;
        end
        else if (LFSR_MSG_BITS == 31) begin
            assign T1 = 27;
            assign T2 = 30;
        end
        else if (LFSR_MSG_BITS == 32) begin
            assign T1 = 24;
            assign T2 = 25;
            assign T3 = 29;
            assign T4 = 31;
        end
        else if (LFSR_MSG_BITS == 33) begin
            assign T1 = 18;
            assign T2 = 32;
        end
        else if (LFSR_MSG_BITS == 34) begin
            assign T1 = 24;
            assign T2 = 28;
            assign T3 = 29;
            assign T4 = 33;
        end
        else if (LFSR_MSG_BITS == 35) begin
            assign T1 = 32;
            assign T2 = 34;
        end
        else if (LFSR_MSG_BITS == 36) begin
            assign T1 = 25;
            assign T2 = 35;
        end
        else if (LFSR_MSG_BITS == 37) begin
            assign T1 = 30;
            assign T2 = 32;
            assign T3 = 33;
            assign T4 = 36;
        end
        else if (LFSR_MSG_BITS == 38) begin
            assign T1 = 31;
            assign T2 = 34;
            assign T3 = 36;
            assign T4 = 37;
        end
        else if (LFSR_MSG_BITS == 39) begin
            assign T1 = 34;
            assign T2 = 38;
        end
        else if (LFSR_MSG_BITS == 40) begin
            assign T1 = 35;
            assign T2 = 37;
            assign T3 = 38;
            assign T4 = 39;
        end
        else if (LFSR_MSG_BITS == 41) begin
            assign T1 = 37;
            assign T2 = 40;
        end
        else if (LFSR_MSG_BITS == 42) begin
            assign T1 = 38;
            assign T2 = 41;
        end
        else if (LFSR_MSG_BITS == 43) begin
            assign T1 = 40;
            assign T2 = 42;
        end
        else if (LFSR_MSG_BITS == 44) begin
            assign T1 = 39;
            assign T2 = 43;
        end
        else if (LFSR_MSG_BITS == 64) begin
            assign T1 = 59;
            assign T2 = 60;
            assign T3 = 62;
            assign T4 = 63;
        end
        
        else begin
            initial $fatal("Unsupported LFSR_MSG_BITS value: %d", LFSR_MSG_BITS);
        end
    endgenerate

`line 318 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
    generate
        if(NUM_TAPS == 1'b1) begin
            assign final_tap = ~(Q[T2] ^ Q[T3] ^ Q[T4] ^ Q[T1]);
        end 
        else if(NUM_TAPS == 1'b0) begin
            assign final_tap = (Q[T2] ^ Q[T1]);
        end
        else begin
            initial $fatal("Unsupported NUM_TAPS value: %d", NUM_TAPS);
        end
    endgenerate
        
    assign next_Q = {Q[LFSR_MSG_BITS-2:0], final_tap};

`line 332 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
    always_ff @(posedge clk) begin
        if (reset) begin
            state <= IDLE;
            Q <= '0;
        end
        else begin
            if( state == IDLE )          Q <= req_msg;
            else if( state == GEN_VAL ) begin
                if (resp_rdy) Q <= next_Q;
            end
            else                         Q <= Q;
        end
        state <= next_state;
    end

`line 348 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
     
    always_comb begin
        case(state)
            IDLE: begin
                if(reset) next_state = IDLE;
                else if(req_val) next_state = GEN_VAL;
                else next_state = IDLE;
            end

`line 358 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
            GEN_VAL: begin
                if(reset) next_state = IDLE;
                else next_state = GEN_VAL;
            end


`line 364 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
            default: begin
                next_state = IDLE;
            end
        endcase
    end

`line 370 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
     
    always_comb begin
        case(state)
            IDLE: begin
                req_rdy = 1'b1;
                resp_val = 1'b0;
                resp_msg = '0;
            end

`line 379 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
            GEN_VAL: begin
                req_rdy = 1'b0;
                resp_val = 1'b1;
                resp_msg = Q;
            end

`line 385 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
            default: begin
                req_rdy = 1'b0;
                resp_val = 1'b0;
                resp_msg = '0;
            end
        endcase
    end

`line 393 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 0
endmodule

`line 395 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/lfsr/lfsr_galois.v" 2
`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 24 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 24 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
 
 

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
 
 
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
 
 
 
 
 

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
 
 
 
 
 
 
 
 
 
 
 
 

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
 

`line 36 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
module misr #(
    parameter int CUT_MSG_BITS = 32,
    parameter int SIGNATURE_BITS = 32,
    parameter int MAX_OUTPUTS_TO_HASH = 32,
    parameter int SEED = 32'd0,
    parameter int LBIST_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH)
    )(
    input logic clk,
    input logic reset,

`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
     
    input  logic                      cut_req_val,
    input  logic [CUT_MSG_BITS-1:0]   cut_req_msg,
    output logic                      cut_req_rdy,

`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
     
    input logic                       lbist_req_val,
    input logic  [LBIST_MSG_BITS:0]   lbist_req_msg,
    output logic                      lbist_req_rdy,

`line 56 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
     
    output logic                      lbist_resp_val,
    output logic [SIGNATURE_BITS-1:0] lbist_resp_msg,
    input  logic                      lbist_resp_rdy
  );

`line 62 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
   
   
   
   

`line 68 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
  logic [1:0]                           state;
  logic [1:0]                           next_state;
  logic [$clog2(MAX_OUTPUTS_TO_HASH):0] next_outputs_hashed;
  logic [$clog2(MAX_OUTPUTS_TO_HASH):0] outputs_hashed;
  logic [$clog2(MAX_OUTPUTS_TO_HASH):0] outputs_to_hash;
  logic [SIGNATURE_BITS - 1:0]          signature;
  logic [SIGNATURE_BITS - 1:0]          next_signature;
  logic                                 done_hashing;

`line 77 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
   
   
   
   
  localparam [1:0]  IDLE = 2'b00;
  localparam [1:0]  HASH = 2'b01;
  localparam [1:0]  DONE = 2'b10;

`line 85 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
  assign next_signature = (signature^cut_req_msg);
  assign done_hashing = ~(outputs_hashed < (outputs_to_hash));
  assign next_outputs_hashed = outputs_hashed + 1;

`line 90 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
  always_ff @(posedge clk) begin
    if( reset ) begin
      outputs_hashed  <= '0;
      outputs_to_hash <= '0;
      signature       <= '0;
    end
    else begin
      if( state == IDLE && lbist_req_val) begin
        signature       <= SEED;
        outputs_to_hash <= lbist_req_msg;
      end
      else if( cut_req_val && state == HASH ) begin
        signature       <= {next_signature[SIGNATURE_BITS-2:0],next_signature[SIGNATURE_BITS-1]};
        outputs_hashed  <= next_outputs_hashed;
      end
      else if (state == DONE) begin
        outputs_hashed  <= '0;
      end
    end
  end

`line 111 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
 
   
  always_ff @(posedge clk) begin
    if( reset ) begin
      state <= IDLE;
    end
    else begin
      state <= next_state;
    end
  end

`line 122 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
   
  always_comb begin
  case ( state )
    IDLE: if( lbist_req_val ) next_state = HASH;
          else next_state = IDLE;

`line 128 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
    HASH: if( ~done_hashing ) next_state = HASH;
          else next_state = DONE;

`line 131 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
    DONE: if( lbist_resp_rdy ) next_state = IDLE;
          else next_state = DONE;

`line 134 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
  default: begin next_state = IDLE; end
  endcase
  end

`line 138 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
   
  always_comb begin
  case ( state )
    IDLE: begin
      cut_req_rdy = 0;              
      lbist_req_rdy = 1;            
      lbist_resp_val = 0;           
      lbist_resp_msg = '0;          
    end

`line 148 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
    HASH: begin
      cut_req_rdy = 1;              
      lbist_req_rdy = 0;            
      lbist_resp_val = 0;           
      lbist_resp_msg = '0;          
    end

`line 155 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
    DONE: begin
      cut_req_rdy = 0;              
      lbist_req_rdy = 0;            
      lbist_resp_val = 1;           
      lbist_resp_msg = signature;   
    end

`line 162 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
     
    default: begin
      cut_req_rdy = 0;
      lbist_req_rdy = 1;
      lbist_resp_val = 0;
      lbist_resp_msg = '0;
    end
  endcase
  end

`line 172 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 0
endmodule
  

`line 175 "/home/jjm469/c2s2/sp25_tapein1/src/lbist/misr/misr.v" 2
`line 24 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
 
 
 
 

`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
 
`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 
 

`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 
 

`line 15 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
 





`line 21 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
           


`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
       







`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
             


`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
           







`line 55 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
     
 
                     
         
          
                       


`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
         







`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
  
           
     
 
                       
                     
           
            
                         


`line 83 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
               



`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 0
   


`line 90 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/regs.v" 2
`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0


`line 9 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
 
 

`line 12 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
module cmn_reset_synchronizer (
  input  logic clk,
  input  logic reset,
  output logic s_reset
);

`line 18 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
   
  logic out_reset_reg0,
        out_reset_reg1;

`line 22 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
   
  cmn_Reg reg0 (
    .clk (clk),
    .q   (out_reset_reg0),
    .d   (reset)
  );

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
  cmn_Reg reg1 (
    .clk (clk),
    .q   (out_reset_reg1),
    .d   (out_reset_reg0)
  );

`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
   
  assign s_reset = out_reset_reg1 | reset;
  
endmodule

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 0
  
`line 41 "/home/jjm469/c2s2/sp25_tapein1/src/cmn/reset_sync.v" 2
`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
 
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 0
 
 
 
module Mem1r1w #(
    parameter p_num_entries = 8,
    parameter p_bit_width = 5,
    parameter p_addr_width = $clog2(p_num_entries)
)
(
    input   logic                     clk,
    input   logic                     reset,
    input   logic                     write_en,
    input   logic [p_addr_width-1:0]  write_addr,
    input   logic [ p_bit_width-1:0]  write_data,
    input   logic                     read_en,
    input   logic [p_addr_width-1:0]  read_addr,
    output  logic [ p_bit_width-1:0]  read_data
);

`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 0
    logic [p_bit_width-1:0] mem [p_num_entries-1:0];

`line 25 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 0
    always_ff @(posedge clk) begin
        if (write_en & ~reset) begin
            mem[int'(write_addr)] <= write_data;
        end
    end

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 0
    assign read_data = mem[int'(read_addr)] & {p_bit_width{read_en}};

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 0
endmodule

`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 0
  

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Mem1r1w.sv" 2
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
 
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
 
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
 
 
 
 
module Synchronizer #(
    parameter p_bit_width = 1
) (
    input   logic                   clk,
    input   logic                   reset,
    input   logic [p_bit_width-1:0]   d,
    output  logic [p_bit_width-1:0]   q
);

`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
    logic [p_bit_width-1:0] s;

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
    always_ff @(posedge clk) begin
        if (reset) begin
            s <= 0;
            q <= 0;
        end else begin
            s <= d;
            q <= s;
        end
    end

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
endmodule

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
  

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 2
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
 
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 0
 
 
 
module BinToGray #(
    parameter p_bit_width = 3
) (
    input   logic [p_bit_width-1:0]   bin,
    output  logic [p_bit_width-1:0]   gray
);
    assign gray = bin ^ (bin >> 1);
endmodule

`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 0
  


`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 2
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
 
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
 
 
 
module ResetSync (
    input  logic  clk,
    input  logic  async_rst,
    output logic  reset
);

`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
logic reg1;
logic reg2;

`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
always @(posedge clk or posedge async_rst) begin
    if (async_rst) begin
        reg1 <= 1'b1;
        reg2 <= 1'b1;
    end else begin
        reg1 <= 1'b0;
        reg2 <= reg1;
    end
end

`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
assign reset = reg2;

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
endmodule

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
  

`line 32 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 2
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0


`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
 
 
 
module WritePtrBlk #(
    parameter p_num_entries = 8,
    parameter p_ptr_width = $clog2(p_num_entries) + 1,  
    parameter p_inc_per_posedge = 1
)
(
    input   logic                     clk,
    input   logic                     async_rst,

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    output  logic [p_ptr_width-1:0]   b_write_ptr,
    output  logic [p_ptr_width-1:0]   g_write_ptr,

`line 23 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    input   logic [p_ptr_width-1:0]   g_read_ptr_async,
    input   logic                     w_en,
    output  logic                     full
);

`line 28 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    logic reset;  

`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    ResetSync reset_sync (
        .clk(clk),
        .async_rst(async_rst),
        .reset(reset)
    );

`line 36 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    logic [p_ptr_width-1:0] g_read_ptr;  

`line 38 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    Synchronizer #(
        .p_bit_width(p_ptr_width)
    ) synch (
        .clk(clk),
        .reset(reset),
        .d(g_read_ptr_async),
        .q(g_read_ptr)
    );

`line 47 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    logic [p_ptr_width-1:0] b_write_ptr_next;
    logic [p_ptr_width-1:0] g_write_ptr_next;

`line 50 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    assign b_write_ptr_next = b_write_ptr + {{(p_ptr_width-1){1'b0}},(w_en && !full)};

`line 52 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    BinToGray #(
        .p_bit_width(p_ptr_width)
    ) bin_to_gray (
        .bin(b_write_ptr_next),
        .gray(g_write_ptr_next)
    );

`line 59 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            b_write_ptr <= 0;
            g_write_ptr <= 0;
        end else begin
            b_write_ptr <= b_write_ptr_next;
            g_write_ptr <= g_write_ptr_next;
        end
    end

`line 69 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
    assign full = (g_write_ptr[p_ptr_width-1:p_ptr_width-2] == ~g_read_ptr[p_ptr_width-1:p_ptr_width-2])
                && (g_write_ptr[p_ptr_width-3:0] == g_read_ptr[p_ptr_width-3:0]);
endmodule

`line 73 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 0
  

`line 75 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/WritePtrBlk.sv" 2
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
 
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
 

`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
 
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
 





`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
  
       
 
                          
                          
           
          


`line 17 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
      

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
       
          
              
              
          
              
              
        
    



`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 0
  

`line 33 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/Synchronizer.sv" 2
`line 4 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0

`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
 
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 0
 




`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 0
  
       
 
           
          

`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 0
           


`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 0
  


`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/BinToGray.sv" 2
`line 5 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0

`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
 
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
 




`line 7 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
  
        
        
       


`line 13 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
 
 

`line 16 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
      
      
          
          
      
          
          
    


`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
   



`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 0
  

`line 32 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ResetSync.sv" 2
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0


`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
 
 
 
module ReadPtrBlk #(
    parameter p_num_entries = 8,
    parameter p_ptr_width = $clog2(p_num_entries) + 1  
)
(
    input   logic                     clk,
    input   logic                     async_rst,

`line 19 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    output  logic [p_ptr_width-1:0]   b_read_ptr,
    output  logic [p_ptr_width-1:0]   g_read_ptr,

`line 22 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    input   logic [p_ptr_width-1:0]   g_write_ptr_async,
    input   logic                     r_en,
    output  logic                     empty
);

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    logic reset;

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    ResetSync reset_sync (
        .clk(clk),
        .async_rst(async_rst),
        .reset(reset)
    );

`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    logic [p_ptr_width-1:0] g_write_ptr;

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    Synchronizer #(
        .p_bit_width(p_ptr_width)
    ) synch (
        .clk(clk),
        .reset(reset),
        .d(g_write_ptr_async),
        .q(g_write_ptr)
    );

`line 46 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    logic [p_ptr_width-1:0] b_read_ptr_next;
    logic [p_ptr_width-1:0] g_read_ptr_next;

`line 49 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    assign b_read_ptr_next = b_read_ptr + {{(p_ptr_width-1){1'b0}},(r_en && !empty)};

`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    BinToGray #(
        .p_bit_width(p_ptr_width)
    ) bin_to_gray (
        .bin(b_read_ptr_next),
        .gray(g_read_ptr_next)
    );
        
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            b_read_ptr <= 0;
            g_read_ptr <= 0;
        end 
        else begin
            b_read_ptr <= b_read_ptr_next;
            g_read_ptr <= g_read_ptr_next;
        end 
    end

`line 69 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
    assign empty = reset || (g_read_ptr == g_write_ptr);
endmodule

`line 72 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 0
  

`line 74 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/ReadPtrBlk.sv" 2
`line 6 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0


`line 8 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
 
 
 
module AsyncFifo #(
    parameter p_num_entries = 8,
    parameter p_bit_width = 8
)
(
    input   logic                     i_clk,
    input   logic                     o_clk,
    input   logic                     async_rst,

`line 20 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    input   logic [p_bit_width-1:0]   istream_msg,
    input   logic                     istream_val,
    output  logic                     istream_rdy,

`line 24 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    output  logic [p_bit_width-1:0]   ostream_msg,
    output  logic                     ostream_val,
    input   logic                     ostream_rdy
);

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    localparam ptr_width = $clog2(p_num_entries) + 1;

`line 31 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    logic full, empty;
    logic [ptr_width-1:0] g_write_ptr;
    logic [ptr_width-1:0] g_read_ptr;

`line 35 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    /*verilator lint_off UNUSED*/ 
    logic [ptr_width-1:0] b_write_ptr;
    logic [ptr_width-1:0] b_read_ptr;
    /*verilator lint_on UNUSED*/ 

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    Mem1r1w #(
        .p_num_entries(p_num_entries),
        .p_bit_width(p_bit_width)
    ) mem1r1w (
        .clk(i_clk),
        .reset(async_rst),
        .write_en(istream_val && istream_rdy),
        .write_addr(b_write_ptr[ptr_width-2:0]),
        .write_data(istream_msg),
        .read_en(ostream_val),
        .read_addr(b_read_ptr[ptr_width-2:0]),
        .read_data(ostream_msg)
    );

`line 54 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    WritePtrBlk #(
        .p_num_entries(p_num_entries)
    ) write_ptr (
        .g_read_ptr_async(g_read_ptr),
        .clk(i_clk),
        .async_rst(async_rst),
        .w_en(istream_val && istream_rdy),
        .*
    );

`line 64 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    ReadPtrBlk #(
        .p_num_entries(p_num_entries)
    ) read_ptr (
        .g_write_ptr_async(g_write_ptr),
        .clk(o_clk),
        .async_rst(async_rst),
        .r_en(ostream_rdy && ostream_val),
        .*
    );

`line 74 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
    assign istream_rdy = !full;
    assign ostream_val = !empty;

`line 77 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
endmodule

`line 79 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 0
  

`line 81 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/AsyncFifo.sv" 2
`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0

`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
 
`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
`line 1 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 1
 
`line 2 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

`line 26 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
 
 

`line 29 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
module FifoPackager #(
    parameter p_bit_width = 3,
    parameter p_num_concat = 2
) (
    input  logic                       clk,
    input  logic                       reset,

`line 36 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
    input  logic [p_bit_width-1:0]     req_msg,
    input  logic                       req_val,
    output logic                       req_rdy,

`line 40 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
    output logic [(p_bit_width*2)-1:0] resp_msg,
    output logic                       resp_val,
    input logic                        resp_rdy
);

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
 
   
   
  logic [p_bit_width-1:0]          out [p_num_concat];
  logic [$clog2(p_num_concat):0]   counter;

`line 51 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
 
  always_comb begin
    for (int i = 0; i < p_num_concat; i = i + 1) begin
        resp_msg[i*p_bit_width +: p_bit_width] = out[i];
    end
  end
  assign resp_val = counter >= p_num_concat;
  assign req_rdy  = counter < p_num_concat;

`line 60 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
 
always_ff @(posedge clk) begin
    if(reset) begin
      for (int i = 0; i < p_num_concat; i = i + 1) begin
        out[i] <= '0;
      end
      counter <= '0;
    end
    else begin
        if(req_val && (counter < p_num_concat)) begin
            out[counter] <= req_msg;
            counter      <= counter + 1;
        end
        if(counter >= p_num_concat && resp_rdy) begin
            counter <= 0;
        end
    end
  end


`line 80 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
endmodule

`line 82 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 0
  


`line 85 "/home/jjm469/c2s2/sp25_tapein1/src/async_fifo/FifoPackager.sv" 2
`line 27 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0



`line 30 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
module tapein1_sp25_top #(
  parameter int FIFO_ENTRY_BITS = 8
) (
   
  input  logic  clk,
  input  logic  reset,

`line 37 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  input  logic  cs,
  input  logic  mosi,
  output logic  miso,
  input  logic  sclk,
  output logic  minion_parity,
  output logic  adapter_parity,

`line 45 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  input  logic                         ext_clk,
  input  logic [FIFO_ENTRY_BITS-1:0]   async_fifo_recv_msg,
   
  input  logic                         async_fifo_recv_val,
  output logic                         async_fifo_recv_rdy
);

`line 53 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   
   
   
  localparam int ADDR_BITS   = 4;
  localparam int DATA_BITS   = 16;
  localparam int SPI_PACKET_BITS = DATA_BITS + ADDR_BITS;

`line 69 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
  localparam int ROUTER_SIZE = 1 << ADDR_BITS;
  localparam int ROUTER_PACKET_BITS = DATA_BITS + ADDR_BITS;


`line 78 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
  localparam int ARBITER_SIZE = ROUTER_SIZE;
  localparam int ARBITER_PACKET_BITS = DATA_BITS;


`line 87 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   

`line 97 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  localparam int INPUT_XBAR_INPUTS = 3;
  localparam int INPUT_XBAR_OUTPUTS = 3;
  localparam int INPUT_XBAR_BITS = DATA_BITS;
  localparam int INPUT_XBAR_CONTROL_BITS = $clog2( INPUT_XBAR_INPUTS *
                                                   INPUT_XBAR_OUTPUTS );

`line 103 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   

`line 113 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  localparam int CLASSIFIER_XBAR_INPUTS = 3;
  localparam int CLASSIFIER_XBAR_OUTPUTS = 3;
  localparam int CLASSIFIER_XBAR_BITS = DATA_BITS;
  localparam int CLASSIFIER_XBAR_CONTROL_BITS = $clog2( CLASSIFIER_XBAR_INPUTS *
                                                        CLASSIFIER_XBAR_OUTPUTS );

`line 119 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   

`line 129 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  localparam int OUTPUT_XBAR_INPUTS = 2;
  localparam int OUTPUT_XBAR_OUTPUTS = 2;
  localparam int OUTPUT_XBAR_BITS = 1;
  localparam int OUTPUT_XBAR_CONTROL_BITS = $clog2( OUTPUT_XBAR_INPUTS *
                                                    OUTPUT_XBAR_OUTPUTS );

`line 135 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
  localparam int FFT1_SAMPLES = 32;
  localparam int FFT1_DECIMAL_PT = 8;


`line 146 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
  localparam int FFT2_SAMPLES = 32;
  localparam int FFT2_DECIMAL_PT = 8;

`line 156 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
  localparam int CLASSIFIER_SAMPLES = 16;
  localparam int CLASSIFIER_BITS = 16;
  localparam int CLASSIFIER_DECIMAL_PT = 8;

`line 169 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
  localparam int SEED_BITS = DATA_BITS;
  localparam int SIGNATURE_BITS = DATA_BITS;
  localparam int NUM_SEEDS = 2;
  localparam int NUM_HASHES = 80;
  localparam int MAX_OUTPUTS_TO_HASH = 100;
  localparam [SEED_BITS-1:0] LFSR_SEEDS [NUM_SEEDS-1:0] = {
    16'b0000000000000000,
    16'b0000000000000000
  };
  localparam [SIGNATURE_BITS-1:0] EXPECTED_SIGNATURES [NUM_SEEDS-1:0] = {
      16'b1100111001111011,
      16'b1100101001001101
  };

`line 203 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
  localparam int MISR_SEED = '0;
  localparam int MISR_MSG_BITS = $clog2(MAX_OUTPUTS_TO_HASH);

`line 212 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
  localparam int FIFO_DEPTH = 10;


`line 220 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
  localparam int PACKAGER_BITS = FIFO_ENTRY_BITS;
  localparam int PACKAGER_CONCAT = 2;




`line 231 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
  logic [ADDR_BITS+DATA_BITS-1:0]          spi_recv_msg;
  logic                                    spi_recv_rdy;
  logic                                    spi_recv_val;
  logic [ADDR_BITS+DATA_BITS-1:0]          spi_send_msg;
  logic                                    spi_send_rdy;
  logic                                    spi_send_val;

`line 240 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [ROUTER_PACKET_BITS - 1:0]         router_msg  [ROUTER_SIZE];
  logic                                    router_rdy  [ROUTER_SIZE];
  logic                                    router_val  [ROUTER_SIZE];

`line 245 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [INPUT_XBAR_BITS-1:0]       Router_to_InputXbar_msg;
  logic                                    Router_to_InputXbar_val;
  logic                                    Router_to_InputXbar_rdy;

`line 249 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [CLASSIFIER_XBAR_BITS-1:0]         Router_to_ClassifierXbar_msg;
  logic                                    Router_to_ClassifierXbar_val;
  logic                                    Router_to_ClassifierXbar_rdy;

`line 253 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [OUTPUT_XBAR_BITS-1:0]             Router_to_OutputXbar_msg;
  logic                                    Router_to_OutputXbar_rdy;
  logic                                    Router_to_OutputXbar_val;

`line 257 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [ARBITER_PACKET_BITS-1:0]          Router_to_Arbiter_msg;
  logic                                    Router_to_Arbiter_val;
  logic                                    Router_to_Arbiter_rdy;

`line 261 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [ARBITER_PACKET_BITS-1:0]          arbiter_msg [ARBITER_SIZE];
  logic                                    arbiter_rdy [ARBITER_SIZE];
  logic                                    arbiter_val [ARBITER_SIZE];

`line 266 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [INPUT_XBAR_BITS-1:0]              input_xbar_recv_msg [INPUT_XBAR_INPUTS];
  logic                                    input_xbar_recv_rdy [INPUT_XBAR_INPUTS];
  logic                                    input_xbar_recv_val [INPUT_XBAR_INPUTS];

`line 271 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [INPUT_XBAR_BITS-1:0]              input_xbar_send_msg [INPUT_XBAR_OUTPUTS];
  logic                                    input_xbar_send_rdy [INPUT_XBAR_OUTPUTS];
  logic                                    input_xbar_send_val [INPUT_XBAR_OUTPUTS];

`line 275 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [INPUT_XBAR_CONTROL_BITS-1:0]      input_xbar_control_msg;
  logic                                    input_xbar_control_rdy;
  logic                                    input_xbar_control_val;

`line 279 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [ARBITER_PACKET_BITS-1:0]          InputXbar_to_Arbiter_msg;
  logic                                    InputXbar_to_Arbiter_val;
  logic                                    InputXbar_to_Arbiter_rdy;

`line 283 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [CLASSIFIER_XBAR_BITS-1:0]         classifier_xbar_recv_msg [CLASSIFIER_XBAR_INPUTS];
  logic                                    classifier_xbar_recv_val [CLASSIFIER_XBAR_INPUTS];
  logic                                    classifier_xbar_recv_rdy [CLASSIFIER_XBAR_INPUTS];

`line 288 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [CLASSIFIER_XBAR_BITS-1:0]         classifier_xbar_send_msg [CLASSIFIER_XBAR_OUTPUTS];
  logic                                    classifier_xbar_send_val [CLASSIFIER_XBAR_OUTPUTS];
  logic                                    classifier_xbar_send_rdy [CLASSIFIER_XBAR_OUTPUTS];

`line 292 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [CLASSIFIER_XBAR_CONTROL_BITS-1:0] classifier_xbar_control_msg;
  logic                                    classifier_xbar_control_rdy;
  logic                                    classifier_xbar_control_val;

`line 296 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [ARBITER_PACKET_BITS-1:0]          ClassifierXbar_to_Arbiter_msg;
  logic                                    ClassifierXbar_to_Arbiter_val;
  logic                                    ClassifierXbar_to_Arbiter_rdy;

`line 300 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic                                    output_xbar_recv_msg [OUTPUT_XBAR_INPUTS];
  logic                                    output_xbar_recv_rdy [OUTPUT_XBAR_INPUTS];
  logic                                    output_xbar_recv_val [OUTPUT_XBAR_INPUTS];

`line 305 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic                                    output_xbar_send_msg [OUTPUT_XBAR_OUTPUTS];
  logic                                    output_xbar_send_rdy [OUTPUT_XBAR_OUTPUTS];
  logic                                    output_xbar_send_val [OUTPUT_XBAR_OUTPUTS];

`line 309 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic [OUTPUT_XBAR_CONTROL_BITS-1:0]     output_xbar_control_msg;
  logic                                    output_xbar_control_rdy;
  logic                                    output_xbar_control_val;

`line 313 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic  [ARBITER_PACKET_BITS-1:0]         OutputXbar_to_Arbiter_msg;
  logic                                    OutputXbar_to_Arbiter_val;
  logic                                    OutputXbar_to_Arbiter_rdy;

`line 317 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    fft1_deserializer_recv_msg;
  logic                                    fft1_deserializer_recv_val;
  logic                                    fft1_deserializer_recv_rdy;

`line 322 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    fft1_serializer_send_msg;
  logic                                    fft1_serializer_send_val;
  logic                                    fft1_serializer_send_rdy;

`line 327 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    fft1_recv_msg [FFT1_SAMPLES];
  logic                                    fft1_recv_val;
  logic                                    fft1_recv_rdy;
  logic [DATA_BITS-1:0]                    fft1_send_msg [FFT1_SAMPLES];
  logic                                    fft1_send_val;
  logic                                    fft1_send_rdy;

`line 335 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    fft2_deserializer_recv_msg;
  logic                                    fft2_deserializer_recv_val;
  logic                                    fft2_deserializer_recv_rdy;

`line 340 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    fft2_serializer_send_msg;
  logic                                    fft2_serializer_send_val;
  logic                                    fft2_serializer_send_rdy;

`line 345 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    fft2_recv_msg [FFT2_SAMPLES];
  logic                                    fft2_recv_val;
  logic                                    fft2_recv_rdy;
  logic [DATA_BITS-1:0]                    fft2_send_msg [FFT2_SAMPLES];
  logic                                    fft2_send_val;
  logic                                    fft2_send_rdy;

`line 353 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    classifier_deserializer_recv_msg;
  logic                                    classifier_deserializer_recv_val;
  logic                                    classifier_deserializer_recv_rdy;

`line 358 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    classifier_recv_msg [CLASSIFIER_SAMPLES];
  logic                                    classifier_recv_val;
  logic                                    classifier_recv_rdy;
  logic [DATA_BITS-1:0]                    classifier_config_msg [3];
  logic                                    classifier_config_rdy [3];
  logic                                    classifier_config_val [3];
  logic                                    classifier_send_msg;
  logic                                    classifier_send_val;
  logic                                    classifier_send_rdy;

`line 369 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic                                    lbist_req_val;
  logic                                    lbist_req_rdy;

`line 373 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic                                    lbist_resp_val;
  logic [NUM_SEEDS-1:0]                    lbist_resp_msg;
  logic                                    lbist_resp_rdy;

`line 377 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic                                    ctrl_lfsr_resp_val;
  logic [SEED_BITS-1:0]                    ctrl_lfsr_resp_msg;
  logic                                    ctrl_lfsr_resp_rdy;

`line 381 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic                                    ctrl_misr_req_val;
  logic [MISR_MSG_BITS:0]                  ctrl_misr_req_msg;
  logic                                    ctrl_misr_req_rdy;

`line 385 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic                                    lfsr_cut_reset;

`line 387 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic                                    lfsr_resp_val;
  logic [SEED_BITS-1:0]                    lfsr_resp_msg;
  logic                                    lfsr_resp_rdy;
   
  logic                                    cut_misr_resp_val;
  logic [SIGNATURE_BITS-1:0]               cut_misr_resp_msg;
  logic                                    cut_misr_resp_rdy;

`line 396 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  logic                                    misr_resp_val;
  logic [SIGNATURE_BITS-1:0]               misr_resp_msg;
  logic                                    misr_resp_rdy;

`line 400 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [FIFO_ENTRY_BITS-1:0]              async_fifo_send_msg;
  logic                                    async_fifo_send_val;
  logic                                    async_fifo_send_rdy;

`line 405 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  logic [DATA_BITS-1:0]                    packager_send_msg;
  logic                                    packager_send_val;
  logic                                    packager_send_rdy;







`line 416 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
  spi_Minion #(
    .BIT_WIDTH               (SPI_PACKET_BITS),
    .N_SAMPLES               (1)
  ) minion (
    .clk                     (clk),
    .reset                   (reset),
    .cs                      (cs),
    .mosi                    (mosi),
    .miso                    (miso),
    .sclk                    (sclk),
    .recv_msg                (spi_recv_msg),
    .recv_rdy                (spi_recv_rdy),
    .recv_val                (spi_recv_val),
    .send_msg                (spi_send_msg),
    .send_rdy                (spi_send_rdy),
    .send_val                (spi_send_val),
    .minion_parity           (minion_parity),
    .adapter_parity          (adapter_parity)
  );

`line 438 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  arbiter_router_Router #(
    .nbits                   (ROUTER_PACKET_BITS),
    .noutputs                (ROUTER_SIZE)
  ) router (
    .clk                     (clk),
    .reset                   (reset),
    .istream_val             (spi_send_val),
    .istream_msg             (spi_send_msg),
    .istream_rdy             (spi_send_rdy),
    .ostream_val             (router_val),
    .ostream_msg             (router_msg),
    .ostream_rdy             (router_rdy)
  );

`line 453 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  arbiter_router_Arbiter #(
    .nbits                   (ARBITER_PACKET_BITS),
    .ninputs                 (ARBITER_SIZE)
  ) arbiter (
    .clk                     (clk),
    .reset                   (reset),
    .istream_val             (arbiter_val),
    .istream_msg             (arbiter_msg),
    .istream_rdy             (arbiter_rdy),
    .ostream_val             (spi_recv_val),
    .ostream_msg             (spi_recv_msg),
    .ostream_rdy             (spi_recv_rdy)
  );

`line 468 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  crossbars_Blocking #(
    .BIT_WIDTH               (INPUT_XBAR_BITS),
    .N_INPUTS                (INPUT_XBAR_INPUTS),
    .N_OUTPUTS               (INPUT_XBAR_OUTPUTS)
  ) input_xbar (
    .clk                     (clk),
    .reset                   (reset),
    .recv_msg                (input_xbar_recv_msg),
    .recv_val                (input_xbar_recv_val),
    .recv_rdy                (input_xbar_recv_rdy),
    .send_msg                (input_xbar_send_msg),
    .send_val                (input_xbar_send_val),
    .send_rdy                (input_xbar_send_rdy),
    .control                 (input_xbar_control_msg),
    .control_rdy             (input_xbar_control_rdy),
    .control_val             (input_xbar_control_val)
  );

`line 487 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  crossbars_Blocking #(
    .BIT_WIDTH               (CLASSIFIER_XBAR_BITS),
    .N_INPUTS                (CLASSIFIER_XBAR_INPUTS),
    .N_OUTPUTS               (CLASSIFIER_XBAR_OUTPUTS)
  ) classifier_xbar (
    .clk                     (clk),
    .reset                   (reset),
    .recv_msg                (classifier_xbar_recv_msg),
    .recv_val                (classifier_xbar_recv_val),
    .recv_rdy                (classifier_xbar_recv_rdy),
    .send_msg                (classifier_xbar_send_msg),
    .send_val                (classifier_xbar_send_val),
    .send_rdy                (classifier_xbar_send_rdy),
    .control                 (classifier_xbar_control_msg),
    .control_rdy             (classifier_xbar_control_rdy),
    .control_val             (classifier_xbar_control_val)
  );

`line 506 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  crossbars_Blocking #(
    .BIT_WIDTH               (OUTPUT_XBAR_BITS),
    .N_INPUTS                (OUTPUT_XBAR_INPUTS),
    .N_OUTPUTS               (OUTPUT_XBAR_OUTPUTS)
  ) output_xbar (
    .clk                     (clk),
    .reset                   (reset),
    .recv_msg                (output_xbar_recv_msg),
    .recv_val                (output_xbar_recv_val),
    .recv_rdy                (output_xbar_recv_rdy),
    .send_msg                (output_xbar_send_msg),
    .send_val                (output_xbar_send_val),
    .send_rdy                (output_xbar_send_rdy),
    .control                 (output_xbar_control_msg),
    .control_rdy             (output_xbar_control_rdy),
    .control_val             (output_xbar_control_val)
  );


`line 526 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  serdes_Deserializer #(
    .N_SAMPLES               (FFT1_SAMPLES),
    .BIT_WIDTH               (DATA_BITS)
  ) fft1_deserializer (
    .clk                     (clk),
    .reset                   (reset || lfsr_cut_reset),
    .recv_val                (fft1_deserializer_recv_val),
    .recv_rdy                (fft1_deserializer_recv_rdy),
    .recv_msg                (fft1_deserializer_recv_msg),
    .send_val                (fft1_recv_val),
    .send_rdy                (fft1_recv_rdy),
    .send_msg                (fft1_recv_msg)
  );

`line 541 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
  serdes_Serializer #(
    .N_SAMPLES               (FFT1_SAMPLES/2),
    .BIT_WIDTH               (DATA_BITS)
  ) fft1_serializer (
    .clk                     (clk),
    .reset                   (reset || lfsr_cut_reset),
    .send_val                (fft1_serializer_send_val),
    .send_rdy                (fft1_serializer_send_rdy),
    .send_msg                (fft1_serializer_send_msg),
    .recv_val                (fft1_send_val),
    .recv_rdy                (fft1_send_rdy),
    .recv_msg                (fft1_send_msg[0:15])
  );

`line 558 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  generate
    for (genvar i = 16; i < 32; i = i + 1) begin
      wire fft1_msg_unused = &{1'b0, fft1_send_msg[i], 1'b0};
    end
  endgenerate

`line 565 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  fft_pease_FFT #(
    .BIT_WIDTH               (DATA_BITS),
    .DECIMAL_PT              (FFT1_DECIMAL_PT),
    .N_SAMPLES               (FFT1_SAMPLES)
  ) fft1 (
    .reset                   (reset || lfsr_cut_reset),
    .clk                     (clk),
    .recv_msg                (fft1_recv_msg),
    .recv_val                (fft1_recv_val),
    .recv_rdy                (fft1_recv_rdy),
    .send_msg                (fft1_send_msg),
    .send_val                (fft1_send_val),
    .send_rdy                (fft1_send_rdy)
  );


`line 582 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   

`line 584 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
  serdes_Deserializer #(
    .N_SAMPLES               (FFT2_SAMPLES),
    .BIT_WIDTH               (DATA_BITS)
  ) fft2_deserializer (
    .clk                     (clk),
    .reset                   (reset || lfsr_cut_reset),
    .recv_val                (fft2_deserializer_recv_val),
    .recv_rdy                (fft2_deserializer_recv_rdy),
    .recv_msg                (fft2_deserializer_recv_msg),
    .send_val                (fft2_recv_val),
    .send_rdy                (fft2_recv_rdy),
    .send_msg                (fft2_recv_msg)
  );

`line 598 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  serdes_Serializer #(
    .N_SAMPLES               (FFT2_SAMPLES/2),
    .BIT_WIDTH               (DATA_BITS)
  ) fft2_serializer (
    .clk                     (clk),
    .reset                   (reset || lfsr_cut_reset),
    .send_val                (fft2_serializer_send_val),
    .send_rdy                (fft2_serializer_send_rdy),
    .send_msg                (fft2_serializer_send_msg),
    .recv_val                (fft2_send_val),
    .recv_rdy                (fft2_send_rdy),
    .recv_msg                (fft2_send_msg[0:15])
  );

`line 613 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  generate
    for (genvar i = 16; i < 32; i = i + 1) begin
      wire fft2_msg_unused = &{1'b0, fft2_send_msg[i], 1'b0};
    end
  endgenerate

`line 620 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  fft_pease_FFT #(
    .BIT_WIDTH               (DATA_BITS),
    .DECIMAL_PT              (FFT2_DECIMAL_PT),
    .N_SAMPLES               (FFT2_SAMPLES)
  ) fft2 (
    .reset                   (reset || lfsr_cut_reset),
    .clk                     (clk),
    .recv_msg                (fft2_recv_msg),
    .recv_val                (fft2_recv_val),
    .recv_rdy                (fft2_recv_rdy),
    .send_msg                (fft2_send_msg),
    .send_val                (fft2_send_val),
    .send_rdy                (fft2_send_rdy)
  );

`line 636 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  serdes_Deserializer #(
    .N_SAMPLES               (CLASSIFIER_SAMPLES),
    .BIT_WIDTH               (DATA_BITS)
  )classifier_deserializer(
    .clk                     (clk),
    .reset                   (reset),
    .recv_val                (classifier_deserializer_recv_val),
    .recv_rdy                (classifier_deserializer_recv_rdy),
    .recv_msg                (classifier_deserializer_recv_msg),
    .send_val                (classifier_recv_val),
    .send_rdy                (classifier_recv_rdy),
    .send_msg                (classifier_recv_msg)
  );

`line 651 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  classifier_Classifier #(
    .BIT_WIDTH               (CLASSIFIER_BITS),
    .DECIMAL_PT              (CLASSIFIER_DECIMAL_PT),
    .N_SAMPLES               (CLASSIFIER_SAMPLES)
  ) classifier (
    .clk                     (clk),
    .reset                   (reset),
    .recv_rdy                (classifier_recv_rdy),
    .recv_val                (classifier_recv_val),
    .recv_msg                (classifier_recv_msg),
    .cutoff_freq_rdy         (classifier_config_rdy[0]),
    .cutoff_freq_val         (classifier_config_val[0]),
    .cutoff_freq_msg         (classifier_config_msg[0]),
    .cutoff_mag_rdy          (classifier_config_rdy[1]),
    .cutoff_mag_val          (classifier_config_val[1]),
    .cutoff_mag_msg          (classifier_config_msg[1]),
    .sampling_freq_rdy       (classifier_config_rdy[2]),
    .sampling_freq_val       (classifier_config_val[2]),
    .sampling_freq_msg       (classifier_config_msg[2]),
    .send_rdy                (classifier_send_rdy),
    .send_val                (classifier_send_val),
    .send_msg                (classifier_send_msg)
  );

`line 676 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  lbist_controller #(
    .SEED_BITS               (SEED_BITS),
    .SIGNATURE_BITS          (SIGNATURE_BITS),
    .NUM_SEEDS               (NUM_SEEDS),
    .NUM_HASHES              (NUM_HASHES),
    .MAX_OUTPUTS_TO_HASH     (MAX_OUTPUTS_TO_HASH),
    .MISR_MSG_BITS           (MISR_MSG_BITS),
    .LFSR_SEEDS              (LFSR_SEEDS),
    .EXPECTED_SIGNATURES     (EXPECTED_SIGNATURES)
  ) lbist_controller (
    .clk                     (clk),
    .reset                   (reset),
    .lbist_req_val           (lbist_req_val),
    .lbist_req_rdy           (lbist_req_rdy),
    .lbist_resp_val          (lbist_resp_val),
    .lbist_resp_msg          (lbist_resp_msg),
    .lbist_resp_rdy          (lbist_resp_rdy),
    .lfsr_resp_val           (ctrl_lfsr_resp_val),
    .lfsr_resp_msg           (ctrl_lfsr_resp_msg),
    .lfsr_resp_rdy           (ctrl_lfsr_resp_rdy),
    .lfsr_cut_reset          (lfsr_cut_reset),
    .misr_req_val            (ctrl_misr_req_val),
    .misr_req_msg            (ctrl_misr_req_msg),
    .misr_req_rdy            (ctrl_misr_req_rdy),
    .misr_resp_val           (misr_resp_val),
    .misr_resp_msg           (misr_resp_msg),
    .misr_resp_rdy           (misr_resp_rdy)
  );

`line 706 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  lfsr_galois #(
    .LFSR_MSG_BITS           (SEED_BITS)
  ) lfsr (
    .clk                     (clk),
    .reset                   (reset || lfsr_cut_reset),
    .req_val                 (ctrl_lfsr_resp_val),
    .req_msg                 (ctrl_lfsr_resp_msg),
    .req_rdy                 (ctrl_lfsr_resp_rdy),
    .resp_rdy                (lfsr_resp_rdy),
    .resp_val                (lfsr_resp_val),
    .resp_msg                (lfsr_resp_msg)
  );

`line 720 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  misr #(
    .CUT_MSG_BITS            (SIGNATURE_BITS),
    .SIGNATURE_BITS          (SIGNATURE_BITS),
    .MAX_OUTPUTS_TO_HASH     (MAX_OUTPUTS_TO_HASH),
    .LBIST_MSG_BITS          (MISR_MSG_BITS),
    .SEED                    (MISR_SEED)
  ) misr (
    .clk                     (clk),
    .reset                   (reset),
    .cut_req_val             (cut_misr_resp_val),
    .cut_req_msg             (cut_misr_resp_msg),
    .cut_req_rdy             (cut_misr_resp_rdy),
    .lbist_req_val           (ctrl_misr_req_val),
    .lbist_req_msg           (ctrl_misr_req_msg),
    .lbist_req_rdy           (ctrl_misr_req_rdy),
    .lbist_resp_val          (misr_resp_val),
    .lbist_resp_msg          (misr_resp_msg),
    .lbist_resp_rdy          (misr_resp_rdy)
  );

`line 741 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  AsyncFifo #(
    .p_num_entries           (FIFO_DEPTH),
    .p_bit_width             (FIFO_ENTRY_BITS)
  ) async_fifo (
    .i_clk                   (ext_clk),
    .o_clk                   (clk),
    .async_rst               (reset),
    .istream_msg             (async_fifo_recv_msg),
    .istream_val             (async_fifo_recv_val),
    .istream_rdy             (async_fifo_recv_rdy),
    .ostream_msg             (async_fifo_send_msg),
    .ostream_val             (async_fifo_send_val),
    .ostream_rdy             (async_fifo_send_rdy)
  );

`line 757 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  FifoPackager #(
    .p_bit_width             (PACKAGER_BITS),
    .p_num_concat            (PACKAGER_CONCAT)
  ) packager (
    .clk                     (clk),
    .reset                   (reset),
    .req_msg                 (async_fifo_send_msg),
    .req_val                 (async_fifo_send_val),
    .req_rdy                 (async_fifo_send_rdy),
    .resp_msg                (packager_send_msg),
    .resp_val                (packager_send_val),
    .resp_rdy                (packager_send_rdy)
  );



`line 774 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   

`line 795 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign lbist_req_val = router_val[0];
  assign router_rdy[0] = lbist_req_rdy;

`line 799 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign Router_to_InputXbar_msg = router_msg[1][ROUTER_PACKET_BITS-1:0];
  assign Router_to_InputXbar_val = router_val[1];
  assign router_rdy[1] = Router_to_InputXbar_rdy;

`line 804 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign input_xbar_control_msg = router_msg[2][INPUT_XBAR_CONTROL_BITS-1:0];
  assign input_xbar_control_val = router_val[2];
  assign router_rdy[2] = input_xbar_control_rdy;

`line 809 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign Router_to_ClassifierXbar_msg = router_msg[3][ROUTER_PACKET_BITS-1:0];
  assign Router_to_ClassifierXbar_val = router_val[3];
  assign router_rdy[3] = Router_to_Arbiter_rdy;

`line 814 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_xbar_control_msg = router_msg[4][CLASSIFIER_XBAR_CONTROL_BITS-1:0];
  assign classifier_xbar_control_val = router_val[4];
  assign router_rdy[4] = classifier_xbar_control_rdy;

`line 819 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_config_msg[0] = router_msg[5][DATA_BITS-1:0];
  assign classifier_config_val[0] = router_val[5];
  assign router_rdy[5] = classifier_config_rdy[0];

`line 824 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_config_msg[1] = router_msg[6][DATA_BITS-1:0];
  assign classifier_config_val[1] = router_val[6];
  assign router_rdy[6] = classifier_config_rdy[1];

`line 829 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_config_msg[2] = router_msg[7][DATA_BITS-1:0];
  assign classifier_config_val[2] = router_val[7];
  assign router_rdy[7] = classifier_config_rdy[2];

`line 834 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign Router_to_OutputXbar_msg = router_msg[8][0];
  assign Router_to_OutputXbar_val = router_val[8];
  assign router_rdy[8] = Router_to_OutputXbar_rdy;

`line 839 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign output_xbar_control_msg = router_msg[9][OUTPUT_XBAR_CONTROL_BITS-1:0];
  assign output_xbar_control_val = router_val[9];
  assign router_rdy[9] = output_xbar_control_rdy;

`line 844 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign Router_to_Arbiter_msg = router_msg[10][ARBITER_PACKET_BITS-1:0];
  assign Router_to_Arbiter_val = router_val[10];
  assign router_rdy[10] = Router_to_Arbiter_rdy;

`line 849 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  generate
    for (genvar i = 11; i < ROUTER_SIZE; i = i + 1) begin
      assign router_rdy[i] = 1'b0;
    end
  endgenerate


`line 857 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   
   

`line 869 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign input_xbar_recv_msg[0] = lfsr_resp_msg;
  assign input_xbar_recv_val[0] = lfsr_resp_val;
  assign lfsr_resp_rdy = input_xbar_recv_rdy[0];

`line 874 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
  assign input_xbar_recv_msg[1] = packager_send_msg;
  assign input_xbar_recv_val[1] = packager_send_val;
  assign packager_send_rdy = input_xbar_recv_rdy[1];

`line 880 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign input_xbar_recv_msg[2] = Router_to_InputXbar_msg;
  assign input_xbar_recv_val[2] = Router_to_InputXbar_val;
  assign Router_to_InputXbar_rdy = input_xbar_recv_rdy[2];


`line 886 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign fft1_deserializer_recv_msg = input_xbar_send_msg[0];
  assign fft1_deserializer_recv_val = input_xbar_send_val[0];
  assign input_xbar_send_rdy[0] = fft1_deserializer_recv_rdy;

`line 891 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign fft2_deserializer_recv_msg = input_xbar_send_msg[1];
  assign fft2_deserializer_recv_val = input_xbar_send_val[1];
  assign input_xbar_send_rdy[1] = fft2_deserializer_recv_rdy;

`line 896 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign InputXbar_to_Arbiter_msg = input_xbar_send_msg[2];
  assign InputXbar_to_Arbiter_val = input_xbar_send_val[2];
  assign input_xbar_send_rdy[2] = InputXbar_to_Arbiter_rdy;


`line 902 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   
   

`line 914 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_xbar_recv_msg[0] = fft1_serializer_send_msg;
  assign classifier_xbar_recv_val[0] = fft1_serializer_send_val;
  assign fft1_serializer_send_rdy = classifier_xbar_recv_rdy[0];

`line 919 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_xbar_recv_msg[1] = fft2_serializer_send_msg;
  assign classifier_xbar_recv_val[1] = fft2_serializer_send_val;
  assign fft2_serializer_send_rdy = classifier_xbar_recv_rdy[1];

`line 924 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_xbar_recv_msg[2] = Router_to_ClassifierXbar_msg;
  assign classifier_xbar_recv_val[2] = Router_to_ClassifierXbar_val;
  assign Router_to_ClassifierXbar_rdy = classifier_xbar_recv_rdy[2];


`line 930 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign cut_misr_resp_msg = classifier_xbar_send_msg[0];
  assign cut_misr_resp_val = classifier_xbar_send_val[0];
  assign classifier_xbar_send_rdy[0] = cut_misr_resp_rdy;

`line 935 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign classifier_deserializer_recv_msg = classifier_xbar_send_msg[1];
  assign classifier_deserializer_recv_val = classifier_xbar_send_val[1];
  assign classifier_xbar_send_rdy[1] = classifier_deserializer_recv_rdy;

`line 940 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign ClassifierXbar_to_Arbiter_msg = classifier_xbar_send_msg[2];
  assign ClassifierXbar_to_Arbiter_val = classifier_xbar_send_val[2];
  assign classifier_xbar_send_rdy[2] = ClassifierXbar_to_Arbiter_rdy;


`line 946 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   

`line 957 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign output_xbar_recv_msg[0] = classifier_send_msg;
  assign output_xbar_recv_val[0] = classifier_send_val;
  assign classifier_send_rdy = output_xbar_recv_rdy[0];

`line 962 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign output_xbar_recv_msg[1] = Router_to_OutputXbar_msg;
  assign output_xbar_recv_val[1] = Router_to_OutputXbar_val;
  assign Router_to_OutputXbar_rdy = output_xbar_recv_rdy[1];


`line 968 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign OutputXbar_to_Arbiter_msg = {15'b0, output_xbar_send_msg[0]};
  assign OutputXbar_to_Arbiter_val = output_xbar_send_val[0];
  assign output_xbar_send_rdy[0] = OutputXbar_to_Arbiter_rdy;

`line 973 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign output_xbar_send_rdy[1] = '0;

`line 976 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   
   

`line 999 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign arbiter_msg[0] = Router_to_Arbiter_msg;
  assign arbiter_val[0] = Router_to_Arbiter_val;
  assign Router_to_Arbiter_rdy = arbiter_rdy[0];

`line 1004 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign arbiter_msg[1] = InputXbar_to_Arbiter_msg;
  assign arbiter_val[1] = InputXbar_to_Arbiter_val;
  assign InputXbar_to_Arbiter_rdy = arbiter_rdy[1];

`line 1009 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign arbiter_msg[2] = ClassifierXbar_to_Arbiter_msg;
  assign arbiter_val[2] = ClassifierXbar_to_Arbiter_val;
  assign ClassifierXbar_to_Arbiter_rdy = arbiter_rdy[2];

`line 1014 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign arbiter_msg[3] = OutputXbar_to_Arbiter_msg;
  assign arbiter_val[3] = OutputXbar_to_Arbiter_val;
  assign OutputXbar_to_Arbiter_rdy = arbiter_rdy[3];

`line 1019 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  assign arbiter_msg[4] = lbist_resp_msg;
  assign arbiter_val[4] = lbist_resp_val;
  assign lbist_resp_rdy = arbiter_rdy[4];

`line 1024 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  generate
    for (genvar i = 5; i < ARBITER_SIZE; i = i + 1) begin
      assign arbiter_msg[i] = 16'b0;
      assign arbiter_val[i] = 1'b0;
    end
  endgenerate

`line 1032 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   


`line 1039 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
  generate
    if (INPUT_XBAR_CONTROL_BITS > DATA_BITS) begin
      $error("INPUT_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
    end
  endgenerate

`line 1050 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  generate
    if (CLASSIFIER_XBAR_CONTROL_BITS > DATA_BITS) begin
      $error("CLASSIFIER_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
    end
  endgenerate

`line 1057 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
  generate
    if (OUTPUT_XBAR_CONTROL_BITS > DATA_BITS) begin
      $error("OUTPUT_XBAR_CONTROL_BITS must be less than or equal to DATA_BITS");
    end
  endgenerate

`line 1064 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
   
   
   
   
   
   
   
   
   
   
   
   
   
   



`line 1081 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 0
endmodule



`line 1085 "/home/jjm469/c2s2/sp25_tapein1/src/tapeins/sp25/tapein1/tapein1_sp25_top.v" 2
`line 2 "top_synth_openlane.sv" 0


`line 4 "top_synth_openlane.sv" 0
module top_synth #(
  parameter int FIFO_ENTRY_BITS = 8
) (
     
     
          
          
    

`line 13 "top_synth_openlane.sv" 0
    input  logic  clk,
    input  logic  reset,

`line 16 "top_synth_openlane.sv" 0
     
    input  logic  cs,
    input  logic  mosi,
    output logic  miso,
    input  logic  sclk,
    output logic  minion_parity,
    output logic  adapter_parity,

`line 24 "top_synth_openlane.sv" 0
     
    input  logic                         ext_clk,
    input  logic [FIFO_ENTRY_BITS-1:0]   async_fifo_recv_msg,
     
    input  logic                         async_fifo_recv_val,
    output logic                         async_fifo_recv_rdy
  );



`line 34 "top_synth_openlane.sv" 0
  tapein1_sp25_top #(
    .FIFO_ENTRY_BITS(FIFO_ENTRY_BITS)
  ) top (
    .clk(clk),
    .reset(reset),
    .cs(cs),
    .mosi(mosi),
    .miso(miso),
    .sclk(sclk),
    .minion_parity(minion_parity),
    .adapter_parity(adapter_parity),
    .ext_clk(ext_clk),
    .async_fifo_recv_msg(async_fifo_recv_msg),
    .async_fifo_recv_val(async_fifo_recv_val),
    .async_fifo_recv_rdy(async_fifo_recv_rdy)
  );

`line 51 "top_synth_openlane.sv" 0
endmodule


`line 54 "top_synth_openlane.sv" 2
