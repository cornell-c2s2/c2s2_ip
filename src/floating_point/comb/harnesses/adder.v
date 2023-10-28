// //================================================
// // comb_float_adder.v
// // 
// // Combinational floating point multiplier
// // Author: Vicky Le (vml37)
// // Additional credits: Barry Lyu (fl327), Xilai Dai (xd44)
// //================================================

// `ifndef COMB_FLOAT_ADDER_HARNESS
// `define COMB_FLOAT_ADDER_HARNESS

// module Comb_float_adder_harness #(
//   parameter int BIT_WIDTH = 32
// ) (
//   input logic [2*BIT_WIDTH - 1:0] recv_msg,
//   output logic [BIT_WIDTH - 1:0] result  // Result of the addition
// );

//   logic [BIT_WIDTH-1:0] a;
//   assign a = recv_msg[2*BIT_WIDTH-1:BIT_WIDTH];

//   logic [BIT_WIDTH-1:0] b;
//   assign b = recv_msg[BIT_WIDTH-1:0];


//   Comb_float_adder #(
//     .BIT_WIDTH(BIT_WIDTH)
//   ) adder (
//     .a(a),  // operand A
//     .b(b),  // operand B
//     .result(result)  // Result of the addition
//   );

// endmodule


// `endif
