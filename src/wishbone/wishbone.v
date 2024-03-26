//========================================================================
// Register Array Implementation
//========================================================================

`ifndef REG_ARRAY_V
`define REG_ARRAY_V
`define CMN_QUEUE_NORMAL 4'b0000

`include "cmn/trace.v"
`include "cmn/regs.v"
`include "cmn/queues.v"

module wishbone_Wishbone #(
  // parameter p_msg_nbits = 1,
  parameter p_num_msgs = 2,
  parameter p_num_istream = 2,
  parameter p_num_ostream = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_msgs),
  parameter istream_addr_nbits = $clog2(p_num_istream),
  parameter ostream_addr_nbits = $clog2(p_num_ostream)
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
  /////////////////
  // address decoder
  //////////////////
  localparam [31:0] ISTREAM_BASE = 32'h3000_0000;  // istream base address
  localparam [31:0] OSTREAM_BASE = ISTREAM_BASE + p_num_istream * 8;  // ostream base address

  logic transaction_val;
  assign transaction_val = wbs_stb_i && wbs_cyc_i;

  logic is_check_istream;
  assign is_check_istream = (wbs_adr_i >= ISTREAM_BASE)
    && (wbs_adr_i < OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'b0)
    && transaction_val && !wbs_we_i;
  logic [istream_addr_nbits-1:0] istream_check_ind;
  assign istream_check_ind = wbs_adr_i >> 3;

  logic is_write_istream;
  assign is_write_istream = (wbs_adr_i >= ISTREAM_BASE)
    && (wbs_adr_i < OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'd4)
    && transaction_val && wbs_we_i;
  logic [istream_addr_nbits-1:0] istream_write_ind;
  assign istream_write_ind = wbs_adr_i >> 3;

  logic is_check_ostream;
  assign is_check_ostream = (wbs_adr_i >= OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'b0)
    && transaction_val
    && !wbs_we_i;
  logic [ostream_addr_nbits-1:0] ostream_check_ind;
  assign ostream_check_ind = (wbs_adr_i - OSTREAM_BASE) >> 3;

  logic is_read_ostream;
  assign is_read_ostream = (wbs_adr_i >= OSTREAM_BASE)
    && (wbs_adr_i[2:0] == 3'd4)
    && transaction_val
    && !wbs_we_i;
  logic [ostream_addr_nbits-1:0] ostream_read_ind;
  assign ostream_read_ind = (wbs_adr_i - OSTREAM_BASE) >> 3;

  /////////////////
  // istream queue
  //////////////////

  logic istream_enq_val[p_num_istream];
  logic istream_enq_rdy[p_num_istream];
  logic [31:0] istream_enq_msg[p_num_istream];

  genvar i;
  generate
    for (i = 0; i < p_num_istream; i++) begin : g_istream_enq_gen
      assign istream_enq_val[i] = (is_write_istream && (istream_write_ind == i)) ? 1'b1 : 1'b0;
      assign istream_enq_msg[i] = (is_write_istream && (istream_write_ind == i)) ? wbs_dat_i : 32'b0;
    end
  endgenerate


  logic [c_addr_nbits:0] istream_num_free_entries[p_num_istream];

  genvar n;
  generate
    for (n = 0; n < p_num_istream; n = n + 1) begin : g_istream_queue_gen
      cmn_Queue #(`CMN_QUEUE_NORMAL, 32, p_num_msgs) istream_queue (
        .clk(clk),
        .reset(reset),
        .enq_val(istream_enq_val[n]),
        .enq_rdy(istream_enq_rdy[n]),
        .enq_msg(wbs_dat_i),
        .deq_val(istream_val[n]),
        .deq_rdy(istream_rdy[n]),
        .deq_msg(istream_data[n]),
        .num_free_entries(istream_num_free_entries[n])
      );
    end
  endgenerate

  //////////////////
  // ostream queue
  //////////////////

  logic [p_num_ostream-1:0] ostream_deq_val;
  logic [p_num_ostream-1:0] ostream_deq_rdy;
  logic [31:0] ostream_deq_msg[p_num_ostream];

  logic [$clog2(p_num_msgs)-1:0] ostream_num_free_entries[p_num_ostream];

  genvar j;
  generate
    for (i = 0; i < p_num_ostream; i++) begin : g_ostream_enq_gen
      assign ostream_deq_rdy[i] = (is_read_ostream && (ostream_read_ind == i)) ? 1'b1 : 1'b0;
    end
  endgenerate

  genvar m;
  generate
    for (m = 0; m < p_num_ostream; m = m + 1) begin : g_ostream_queue_gen
      cmn_Queue #(`CMN_QUEUE_NORMAL, 32, p_num_msgs) ostream_queue (
        .clk(clk),
        .reset(reset),
        .enq_val(ostream_val[m]),
        .enq_rdy(ostream_rdy[m]),
        .enq_msg(ostream_data[m]),
        .deq_val(ostream_deq_val[m]),
        .deq_rdy(ostream_deq_rdy[m]),
        .deq_msg(ostream_deq_msg[m]),
        .num_free_entries(ostream_num_free_entries[m])
      );
    end
  endgenerate


  //////////////
  // set outputs
  /////////////
  always_comb begin
    if (is_check_istream) wbs_dat_o = istream_enq_rdy[istream_check_ind] & {31'b0, 1'b1};
    else if (is_check_ostream) wbs_dat_o = ostream_deq_val[ostream_check_ind] & {31'b0, 1'b1};
    else if (is_read_ostream) wbs_dat_o = ostream_deq_msg[ostream_read_ind];
    else wbs_dat_o = 32'b0;
  end


  assign wbs_ack_o = 1'b1;


  //----------------------------------------------------------------------
  // Input Registers (sequential logic)
  //----------------------------------------------------------------------


`ifndef SYNTHESIS

  logic [`CMN_TRACE_NBITS-1:0] str;
  `CMN_TRACE_BEGIN
  begin

    $sformat(str, "%x", wbs_adr_i);
    cmn_trace.append_str(
        trace_str, str
    ); cmn_trace.append_str(
        trace_str, "|"
    );

    $sformat(str, "%x", is_check_istream);
    cmn_trace.append_str(
        trace_str, str
    ); cmn_trace.append_str(
        trace_str, "|"
    );

    $sformat(str, "%x", is_check_ostream);
    cmn_trace.append_str(
        trace_str, str
    ); cmn_trace.append_str(
        trace_str, "|"
    );

    $sformat(str, "%x", is_read_ostream);
    cmn_trace.append_str(
        trace_str, str
    ); cmn_trace.append_str(
        trace_str, "|"
    );

    $sformat(str, "%x", is_write_istream);
    cmn_trace.append_str(
        trace_str, str
    ); cmn_trace.append_str(
        trace_str, "|"
    );

    $sformat(str, "%x", istream_write_ind);
    cmn_trace.append_str(
        trace_str, str
    ); cmn_trace.append_str(
        trace_str, "|"
    );

    $sformat(str, "%x", wbs_adr_i[3:0]);
    cmn_trace.append_str(
        trace_str, str
    ); cmn_trace.append_str(
        trace_str, "|"
    );

    // $sformat( str, "%x", istream_enq_rdy[2]);
    // cmn_trace.append_str( trace_str, str );
    // cmn_trace.append_str( trace_str, "|" );

    // $sformat( str, "%x", istream_check_ind);
    // cmn_trace.append_str( trace_str, str );
    // cmn_trace.append_str( trace_str, "|" );




  end
  `CMN_TRACE_END

`endif  /* SYNTHESIS */

endmodule

`endif  /* REG_ARRAY_V */
