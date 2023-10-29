//================================================
// wishbone.v
//================================================
`default_nettype none
`ifndef WISHBONE_V
`define WISHBONE_V

module Wishbone #(
  parameter n_modules = 1
) (
  // Wishbone Slave ports (WB MI A)
  input  logic [n_modules-1:0] i_stream_rdy,
  output logic [n_modules-1:0] i_stream_val,

  input logic clk,
  input logic reset,
  input logic wbs_stb_i,
  input logic wbs_cyc_i,
  input logic wbs_we_i,
  input logic [3:0] wbs_sel_i,
  input logic [31:0] wbs_dat_i,
  input logic [31:0] wbs_adr_i,

  output logic [n_modules-1:0] o_stream_rdy,
  input  logic [n_modules-1:0] o_stream_val,

  input  logic [31:0] o_stream_data,
  output logic [31:0] i_stream_data,

  output logic wbs_ack_o,
  output logic [31:0] wbs_dat_o

);

  localparam [31:0] BASE_ADDRESS = 32'h3000_0000;  // base address
  localparam [31:0] FFT_ADDRESS = BASE_ADDRESS + 4;
  localparam [31:0] UPPER_BOUND_ADDRESS = BASE_ADDRESS + 4;

  // Loopback register
  logic [31:0] loopback_reg;
  logic loopback_reg_en;
  always_ff @(posedge clk) begin
    if (reset) begin
      loopback_reg <= 32'b0;
    end else if (loopback_reg_en) begin
      loopback_reg <= wbs_dat_i;
    end
  end


  assign i_stream_data = wbs_dat_i;
  logic wbs_dat_o_sel;
  assign wbs_dat_o = (wbs_dat_o_sel) ? loopback_reg : o_stream_data;

  logic [$clog2(n_modules):0] index;
  assign index = 0;  // hardcoding this for now

  // Logic for states
  logic is_write_module;
  logic is_read_module;
  logic is_write_loop;
  logic is_read_loop;

  always_comb begin  // hardcoding address for now
    is_write_loop = wbs_stb_i && wbs_cyc_i && wbs_we_i && (wbs_adr_i == BASE_ADDRESS);
    is_read_loop = wbs_stb_i && wbs_cyc_i && !wbs_we_i && (wbs_adr_i == BASE_ADDRESS);
    is_write_module = wbs_stb_i && wbs_cyc_i && wbs_we_i && (wbs_adr_i == FFT_ADDRESS);
    is_read_module = wbs_stb_i && wbs_cyc_i && !wbs_we_i && (wbs_adr_i == FFT_ADDRESS);
  end


  //----------------------------------------------------------------------
  // State
  //----------------------------------------------------------------------

  localparam IDLE = 2'd0;
  localparam BUSY = 2'd1;
  localparam DONE = 2'd2;
  localparam LOOP = 2'd3;

  logic [1:0] state, next_state;

  always_ff @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  //----------------------------------------------------------------------
  // State Transitions
  //----------------------------------------------------------------------

  always_comb begin
    next_state = state;
    case (state)
      IDLE: begin
        if (is_write_module) next_state = BUSY;
        else if (is_write_loop) next_state = LOOP;
      end
      BUSY: if (o_stream_val[index]) next_state = DONE;
      DONE: if (is_read_module) next_state = IDLE;
      LOOP: if (is_read_loop) next_state = IDLE;
    endcase
  end

  function void cs(input logic cs_i_stream_val, input logic cs_o_stream_rdy,
                   input logic cs_wbs_ack_o, input logic cs_loopback_reg_en,
                   input logic cs_wbs_dat_o_sel);

    begin
      i_stream_val = cs_i_stream_val;
      o_stream_rdy = cs_o_stream_rdy;
      wbs_ack_o    = cs_wbs_ack_o;
      loopback_reg_en = cs_loopback_reg_en;
      wbs_dat_o_sel = cs_wbs_dat_o_sel;
    end
  endfunction

  always_comb begin
    cs(0, 0, 0, 0, 0);
    case (state)
      IDLE: begin
        if (is_write_module) cs(1, 0, 0, 0, 0);
        else if (is_write_loop) cs(0, 0, 1, 1, 0);
        else cs(0, 0, 0, 0, 0);
      end
      BUSY: begin
        if (o_stream_val) cs(0, 0, 1, 0, 0);
        else cs(0, 0, 0, 0, 0);
      end
      DONE: begin
        if (is_read_module) cs(0, 1, 1, 0, 0);
        else cs(0, 0, 0, 0, 0);
      end
      LOOP: begin
        if (is_read_loop) cs(0, 0, 1, 0, 1);
        else cs(0, 0, 0, 0, 0);
      end
    endcase
  end

endmodule

`endif
