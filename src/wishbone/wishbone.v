//================================================
// wishbone.v
//================================================
`default_nettype none
`ifndef WISHBONE_V
`define WISHBONE_V

`include "cmn/muxes.v"
`include "cmn/regs.v"
`include "cmn/arithmetic.v"

module Wishbone #(
  parameter n_modules = 2
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
  input logic [n_modules-1:0] i_stream_rdy,
  output logic [n_modules-1:0] i_stream_val,
  output logic [n_modules-1:0] o_stream_rdy,
  input logic [n_modules-1:0] o_stream_val,
  input logic [31:0] o_stream_data [n_modules],
  output logic [31:0] i_stream_data [n_modules]

);

  localparam [31:0] BASE_ADDRESS = 32'h3000_0000;  // base address
  localparam [31:0] ERROR_ADDRESS = BASE_ADDRESS + 4;  // base address
  localparam [31:0] FFT_ADDRESS = BASE_ADDRESS + 8;
  localparam [31:0] UPPER_BOUND_ADDRESS = BASE_ADDRESS + ((n_modules << 2) + 8) ;

  // Loopback register
  logic [31:0] loopback_reg;
  logic loopback_reg_en;
  // always_ff @(posedge clk) begin
  //   if (reset) begin
  //     loopback_reg <= 32'b0;
  //   end else if (loopback_reg_en) begin
  //     loopback_reg <= wbs_dat_i;
  //   end
  // end

  cmn_EnResetReg #(32, 0) loopback_enset_reg (
    .clk(clk),
    .reset(reset),
    .q(loopback_reg),
    .d(wbs_dat_i),
    .en(loopback_reg_en)
  );

  ////////////////////
  // Error register //
  ////////////////////
  logic [31:0] error_reg;
  logic [31:0] next_error_reg;
  logic error_reg_en;
  cmn_EnResetReg #(32, 0) error_enset_reg (
    .clk(clk),
    .reset(reset),
    .q(error_reg),
    .d(next_error_reg),
    .en(error_reg_en)
  );
  // always_ff @(posedge clk) begin
  //   if (reset) begin
  //     error_reg <= 32'b0;
  //   end else if (error_reg_en) begin
  //     loopback_reg <= next_error_reg;
  //   end
  // end

  ////////////////////
  // Index register //
  ////////////////////
  logic [$clog2(n_modules)-1:0] index_reg;
  logic index_reg_en;
  cmn_EnResetReg #(32, 0) index_enset_reg (
    .clk(clk),
    .reset(reset),
    .q(index_reg),
    .d(index),
    .en(index_reg_en)
  );
  // always_ff @(posedge clk) begin
  //   if (reset) begin
  //     index_reg <= 0;
  //   end else if (index_reg_en) begin
  //     index_reg <= index;
  //   end
  // end

  ////////////////////////
  // Wishbone data mux //
  ///////////////////////
  // assign i_stream_data = {$clog2(n_modules){wbs_dat_i}};
  genvar i;
  generate
    for (i = 0; i < n_modules; i = i + 1) begin : output_gen
      assign i_stream_data[i] = wbs_dat_i;
    end
  endgenerate

  logic [1:0] wbs_dat_o_sel;
  // always_comb begin
  //   if (wbs_dat_o_sel == 2'd0) wbs_dat_o = loopback_reg;
  //   else if (wbs_dat_o_sel == 2'd1) wbs_dat_o = o_stream_data[index];
  //   else if (wbs_dat_o_sel == 2'd2) wbs_dat_o = o_stream_data[index_reg];
  //   else if (wbs_dat_o_sel == 2'd3) wbs_dat_o = error_reg;
  //   else wbs_dat_o = 31'bx;
  // end

  cmn_Mux4 #( 32 ) wbs_dat_o_mux (
    .in0(loopback_reg),
    .in1(o_stream_data[index]),
    .in2(o_stream_data[index_reg]),
    .in3(error_reg),
    .sel(wbs_dat_o_sel),
    .out(wbs_dat_o)
  );

  logic [$clog2(n_modules)-1:0] index;

  assign index = (wbs_adr_i >> 2) - 4'd12;

  // Logic for states
  logic is_write_module;
  logic is_write_module_error;
  logic is_read_module;
  logic is_read_module_error;
  logic is_read_busy_module;
  logic is_write_loop;
  logic is_read_loop;
  logic is_read_error;

  always_comb begin
    is_write_loop = wbs_stb_i && wbs_cyc_i && wbs_we_i && (wbs_adr_i == BASE_ADDRESS);
    is_read_loop = wbs_stb_i && wbs_cyc_i && !wbs_we_i && (wbs_adr_i == BASE_ADDRESS);
    is_read_error = wbs_stb_i && wbs_cyc_i && !wbs_we_i && (wbs_adr_i == ERROR_ADDRESS);
    is_write_module = wbs_stb_i && wbs_cyc_i && wbs_we_i && i_stream_rdy[index] &&
      (wbs_adr_i <= UPPER_BOUND_ADDRESS && wbs_adr_i > ERROR_ADDRESS && wbs_adr_i[1:0] == 2'b0);
    is_write_module_error = wbs_stb_i && wbs_cyc_i && wbs_we_i && !i_stream_rdy[index] &&
      (wbs_adr_i <= UPPER_BOUND_ADDRESS && wbs_adr_i > ERROR_ADDRESS && wbs_adr_i[1:0] == 2'b0);
    is_read_module = wbs_stb_i && wbs_cyc_i && !wbs_we_i && o_stream_val[index] &&
      (wbs_adr_i <= UPPER_BOUND_ADDRESS && wbs_adr_i > ERROR_ADDRESS && wbs_adr_i[1:0] == 2'b0);
    is_read_module_error = wbs_stb_i && wbs_cyc_i && !wbs_we_i && !o_stream_val[index] && i_stream_rdy[index] &&
      (wbs_adr_i <= UPPER_BOUND_ADDRESS && wbs_adr_i > ERROR_ADDRESS && wbs_adr_i[1:0] == 2'b0);
    is_read_busy_module = wbs_stb_i && wbs_cyc_i && !wbs_we_i && !o_stream_val[index] && !i_stream_rdy[index] &&
      (wbs_adr_i <= UPPER_BOUND_ADDRESS && wbs_adr_i > ERROR_ADDRESS && wbs_adr_i[1:0] == 2'b0);
  end

  //----------------------------------------------------------------------
  // State
  //----------------------------------------------------------------------

  localparam IDLE = 1'd0;
  localparam BUSY = 1'd1;


  logic state, next_state;

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
        if (is_read_busy_module) next_state = BUSY;
        else next_state = IDLE;
      end
      BUSY: if (o_stream_val[index]) next_state = IDLE;
    endcase
  end

  //----------------------------------------------------------------------
  // State Outputs
  //----------------------------------------------------------------------

  localparam [1:0] loop_sel = 2'd0;
  localparam [1:0] data_sel = 2'd1;
  localparam [1:0] data_reg_sel = 2'd2;
  localparam [1:0] error_sel = 2'd3;
  localparam [1:0] x_sel = 2'dx;

  logic [n_modules-1:0] one_index;
  logic [n_modules-1:0] one_index_reg;
  cmn_LeftLogicalShifter #(
    n_modules,
    $clog2(n_modules)
  ) index_reg_shifter (
    .in(32'b1),
    .shamt(index_reg),
    .out(one_index_reg)
  );

  cmn_LeftLogicalShifter #(
    n_modules,
    $clog2(n_modules)
  ) index_shifter (
    .in(32'b1),
    .shamt(index),
    .out(one_index)
  );
  // assign one_index = {n_modules{1'b0}};
  // assign one_index[index] = 1'b1;

  // assign one_index_reg = {n_modules{1'b0}};
  // assign one_index_reg[index_reg] = 1'b1;

  // genvar i;
  // generate
  //   for (i = 0; i < n_modules; i = i + 1) begin : output_gen
  //     assign one_index = (i == sel) ? in : {nbits{1'b0}};
  //   end
  // endgenerate

  task cs(
    // module interface
    input logic [n_modules-1:0] cs_i_stream_val,
    input logic [n_modules-1:0] cs_o_stream_rdy,

    // loopback reg
    input logic cs_loopback_reg_en,

    // error reg
    input logic cs_error_reg_en,
    input logic [31:0] cs_next_error_reg,

    // index reg
    input logic cs_index_reg_en,

    // wb reg
    input logic cs_wbs_ack_o,
    input logic [1:0] cs_wbs_dat_o_sel );
    begin
      i_stream_val = cs_i_stream_val;
      o_stream_rdy = cs_o_stream_rdy;
      loopback_reg_en = cs_loopback_reg_en;
      error_reg_en = cs_error_reg_en;
      next_error_reg = cs_next_error_reg;
      index_reg_en = cs_index_reg_en;
      wbs_ack_o    = cs_wbs_ack_o;
      wbs_dat_o_sel = cs_wbs_dat_o_sel;
    end
  endtask

  always_comb begin
    cs(0, 0, 0, 0, 0, 0, 0, 0);

    case ( state )
    //                                     istream | ostream | loopback | error | error | index | wbs |   wbs
    //                                      val    |  rdy    |  regen   | regen |  reg  | regen | ack | dat sel
      IDLE: begin
        if      (is_read_loop)          cs( 0,        0,         0,       1,       0,      0,     1,    loop_sel);
        else if (is_write_loop)         cs( 0,        0,         1,       1,       0,      0,     1,       x_sel);
        else if (is_read_error)         cs( 0,        0,         0,       0,       0,      0,     1,   error_sel);
        else if (is_read_module)        cs( 0,    one_index,     0,       1,       0,      0,     1,    data_sel);
        else if (is_read_busy_module)   cs( 0,        0,         0,       1,       0,      1,     0,       x_sel);
        else if (is_read_module_error)  cs( 0,        0,         0,       1,       1,      0,     1,       x_sel);
        else if (is_write_module)       cs(one_index, 0,         0,       1,       0,      0,     1,       x_sel);
        else if (is_write_module_error) cs( 0,        0,         0,       1,       1,      0,     1,       x_sel);
      end
      BUSY: begin
        if (o_stream_val[index_reg])    cs( 0,  one_index_reg,   0,       0,       0,      0,     1,data_reg_sel);
        else                            cs( 0,        0,         0,       0,       0,      0,     0,       x_sel);
      end
      default: cs(0, 0, 0, 0, 0, 0, 0, 0);
    endcase
  end



  // //----------------------------------------------------------------------
  // // State
  // //----------------------------------------------------------------------

  // localparam IDLE = 2'd0;
  // localparam BUSY = 2'd1;
  // localparam DONE = 2'd2;
  // localparam LOOP = 2'd3;

  // logic [1:0] state, next_state;

  // always_ff @(posedge clk) begin
  //   if (reset) begin
  //     state <= IDLE;
  //   end else if (next_state == IDLE) begin
  //     state <= IDLE;
  //   end else if (next_state == BUSY) begin
  //     state <= BUSY;
  //   end else if (next_state == DONE) begin
  //     state <= DONE;
  //   end else if (next_state == LOOP) begin
  //     state <= LOOP;
  //   end
  // end

  // //----------------------------------------------------------------------
  // // State Transitions
  // //----------------------------------------------------------------------

  // always_comb begin
  //   next_state = state;
  //   case (state)
  //     IDLE: begin
  //       if (is_write_module) next_state = BUSY;
  //       else if (is_write_loop) next_state = LOOP;
  //     end
  //     BUSY: if (o_stream_val[index]) next_state = DONE;
  //     DONE: if (is_read_module) next_state = IDLE;
  //     LOOP: if (is_read_loop) next_state = IDLE;
  //   endcase
  // end

  // function void cs(input logic cs_i_stream_val, input logic cs_o_stream_rdy,
  //                  input logic cs_wbs_ack_o, input logic cs_loopback_reg_en,
  //                  input logic cs_wbs_dat_o_sel);

  //   begin
  //     i_stream_val = cs_i_stream_val;
  //     o_stream_rdy = cs_o_stream_rdy;
  //     wbs_ack_o    = cs_wbs_ack_o;
  //     loopback_reg_en = cs_loopback_reg_en;
  //     wbs_dat_o_sel = cs_wbs_dat_o_sel;
  //   end
  // endfunction

  // always_comb begin
  //   cs(0, 0, 0, 0, 0);
  //   case (state)
  //     IDLE: begin
  //       if (is_write_module) cs(1, 0, 0, 0, 0);
  //       else if (is_write_loop) cs(0, 0, 1, 1, 0);
  //       else cs(0, 0, 0, 0, 0);
  //     end
  //     BUSY: begin
  //       if (next_state == DONE) cs(0, 0, 1, 0, 0);
  //       else cs(0, 0, 0, 0, 0);
  //     end
  //     DONE: begin
  //       if (is_read_module) cs(0, 1, 1, 0, 1);
  //       else cs(0, 0, 0, 0, 0);
  //     end
  //     LOOP: begin
  //       if (is_read_loop) cs(0, 0, 1, 0, 0);
  //       else cs(0, 0, 0, 0, 0);
  //     end
  //   endcase
  // end

endmodule

`endif
