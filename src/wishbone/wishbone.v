//========================================================================
// Register Array Implementation
//========================================================================

`ifndef REG_ARRAY_V
`define REG_ARRAY_V
`define CMN_QUEUE_NORMAL 4'b0000

`include "cmn/regs.v"
`include "cmn/queues.v"
`include "cmn/arithmetic.v"

module wishbone_Wishbone #(
  // parameter p_msg_nbits = 1,
  parameter int p_num_msgs = 2,
  parameter int p_num_istream = 2,
  parameter int p_num_ostream = 2

) (
  // Wishbone Slave ports (WB MI A)
  input logic clk,
  input logic reset,
  input logic wbs_stb_i,
  input logic wbs_cyc_i,
  input logic wbs_we_i,
  input logic [3:0] wbs_sel_i,
  input logic [31:0] wbs_dat_i,
  input logic [31:0] wbs_adr_i,
  output logic wbs_ack_o,
  output logic [31:0] wbs_dat_o,

  // Ports to connect to modules
  input  logic istream_rdy[p_num_istream],
  output logic istream_val[p_num_istream],

  output logic ostream_rdy[p_num_ostream],
  input  logic ostream_val[p_num_ostream],

  input  logic [31:0] ostream_data[p_num_ostream],
  output logic [31:0] istream_data[p_num_istream]
);

  // Local constants not meant to be set from outside the module
  localparam int c_addr_nbits = $clog2(p_num_msgs);
  localparam int istream_addr_nbits = $clog2(p_num_istream);
  localparam int ostream_addr_nbits = $clog2(p_num_ostream);

  /////////////////
  // address decoder
  //////////////////
  localparam int ISTREAM_BASE = 32'h3000_0000;  // istream base address
  localparam int OSTREAM_BASE = ISTREAM_BASE + p_num_istream * 8;  // ostream base address

  logic transaction_val;
  assign transaction_val = wbs_stb_i && wbs_cyc_i;

  logic [31:0] adr_sub;
  cmn_Subtractor #(32) ostream_addr_sub (
    .in0(wbs_adr_i),
    .in1(OSTREAM_BASE),
    .out(adr_sub)
  );

  logic is_check_istream;
  assign is_check_istream = (wbs_adr_i >= ISTREAM_BASE)
    && (wbs_adr_i < OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'b0)
    && transaction_val && !wbs_we_i;
  logic [istream_addr_nbits-1:0] istream_check_ind;

  logic is_write_istream;
  assign is_write_istream = (wbs_adr_i >= ISTREAM_BASE)
    && (wbs_adr_i < OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'd4)
    && transaction_val && wbs_we_i;
  logic [istream_addr_nbits-1:0] istream_write_ind;

  logic is_check_ostream;
  assign is_check_ostream = (wbs_adr_i >= OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'b0)
    && transaction_val
    && !wbs_we_i;
  logic [ostream_addr_nbits-1:0] ostream_check_ind;

  logic is_read_ostream;
  assign is_read_ostream = (wbs_adr_i >= OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'd4)
    && transaction_val
    && !wbs_we_i;
  logic [ostream_addr_nbits-1:0] ostream_read_ind;

  assign istream_check_ind = wbs_adr_i[istream_addr_nbits-1+3:3];
  assign istream_write_ind = wbs_adr_i[istream_addr_nbits-1+3:3];
  assign ostream_check_ind = adr_sub[ostream_addr_nbits-1+3:3];
  assign ostream_read_ind  = adr_sub[ostream_addr_nbits-1+3:3];

  /////////////////
  // istream queue
  //////////////////

  logic istream_enq_val[p_num_istream];
  logic istream_enq_rdy[p_num_istream];
  logic [31:0] istream_enq_msg[p_num_istream];

  generate
    for (genvar i = 0; i < p_num_istream; i++) begin : g_istream_enq_gen
      assign istream_enq_val[i] = (is_write_istream && (istream_write_ind == i)) ? 1'b1 : 1'b0;
      assign istream_enq_msg[i] = (is_write_istream && (istream_write_ind == i)) ? wbs_dat_i : 32'b0;
    end
  endgenerate


  generate
    for (genvar n = 0; n < p_num_istream; n = n + 1) begin : g_istream_queue_gen
      cmn_Queue #(`CMN_QUEUE_NORMAL, 32, p_num_msgs) istream_queue (
        .clk(clk),
        .reset(reset),
        .enq_val(istream_enq_val[n]),
        .enq_rdy(istream_enq_rdy[n]),
        .enq_msg(istream_enq_msg[n]),
        .deq_val(istream_val[n]),
        .deq_rdy(istream_rdy[n]),
        .deq_msg(istream_data[n]),
        /* verilator lint_off PINCONNECTEMPTY */
        .num_free_entries()
        /* verilator lint_on PINCONNECTEMPTY */
      );
    end
  endgenerate

  //////////////////
  // ostream queue
  //////////////////

  logic [p_num_ostream-1:0] ostream_deq_val;
  logic [p_num_ostream-1:0] ostream_deq_rdy;
  logic [31:0] ostream_deq_msg[p_num_ostream];

  generate
    for (genvar i = 0; i < p_num_ostream; i++) begin : g_ostream_enq_gen
      assign ostream_deq_rdy[i] = (is_read_ostream && (ostream_read_ind == i)) ? 1'b1 : 1'b0;
    end
  endgenerate

  generate
    for (genvar m = 0; m < p_num_ostream; m = m + 1) begin : g_ostream_queue_gen
      cmn_Queue #(`CMN_QUEUE_NORMAL, 32, p_num_msgs) ostream_queue (
        .clk(clk),
        .reset(reset),
        .enq_val(ostream_val[m]),
        .enq_rdy(ostream_rdy[m]),
        .enq_msg(ostream_data[m]),
        .deq_val(ostream_deq_val[m]),
        .deq_rdy(ostream_deq_rdy[m]),
        .deq_msg(ostream_deq_msg[m]),
        /* verilator lint_off PINCONNECTEMPTY */
        .num_free_entries()
        /* verilator lint_on PINCONNECTEMPTY */
      );
    end
  endgenerate


  //////////////
  // set outputs
  /////////////
  always_comb begin
    if (is_check_istream) wbs_dat_o = {31'b0, istream_enq_rdy[istream_check_ind]};
    else if (is_check_ostream) wbs_dat_o = {31'b0, ostream_deq_val[ostream_check_ind]};
    else if (is_read_ostream) wbs_dat_o = ostream_deq_msg[ostream_read_ind];
    else wbs_dat_o = 32'b0;
  end


  assign wbs_ack_o = 1'b1;


  // Unused Net
  logic unused = &{1'b0, wbs_sel_i, adr_sub, 1'b0};
endmodule

`endif  /* REG_ARRAY_V */
