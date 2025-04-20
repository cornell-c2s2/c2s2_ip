//================================================
// drop_unit.v
//================================================
`default_nettype none
`ifndef DROP_UNIT_V
`define DROP_UNIT_V

module drop_unit #(
  parameter int N_BITS = 8,
  parameter int MAX_N_CYCLES = 10  // The max number of cycles the unit waits for before sending a sample
) (
  // Clock and Reset Ports
  input  logic  clk,
  input  logic  reset,
  input  logic  enable,                // If 1, disable drop unit (send every req_msg to resp_msg). In this mode, the drop unit acts basically like a wire.
 
  input  logic [N_BITS-1:0]                req_msg,
  input  logic                             req_val,
  output logic                             req_rdy,
 
  output logic [N_BITS-1:0]                resp_msg,
  output logic                             resp_val,
  input  logic                             resp_rdy,
 
  input  logic [$clog2(MAX_N_CYCLES)-1:0]  cfg_drop_msg, // A counter value to denote the number of cycles between captured samples.
  input  logic                             cfg_drop_val,  // Val signal for above
  output logic                             cfg_drop_rdy
);

  localparam SEND = 2'd0, DROP = 2'd1;
  logic state, next_state;
  
  logic [$clog2(MAX_N_CYCLES)-1:0] n_cycles;
  logic [$clog2(MAX_N_CYCLES)-1:0] counter;

  // manage state
  always_comb begin
    case (state)
      SEND: begin
        if (enable == 0 & req_val == 1 & req_rdy == 1) begin
          next_state = DROP;
        end else begin
          next_state = SEND;
        end
      end
      DROP: begin
        if (counter == n_cycles - 2 || enable == 1) begin
          next_state = SEND;
        end else begin
          next_state = DROP;
        end
      end
      default: begin
        next_state = SEND;
      end
    endcase
  end

  // manage data path
  always_comb begin
    case (state)
      SEND: begin
        req_rdy      = resp_rdy;
        resp_msg     = req_msg;
        resp_val     = req_val;
        cfg_drop_rdy = 1;
      end
      DROP: begin
        req_rdy      = 1;
        resp_msg     = 0;
        resp_val     = 0;
        cfg_drop_rdy = 0;
      end
      default: begin
      end
    endcase
  end

  // reset logic
  always_ff @(posedge clk) begin
    if (reset) begin
        state <= SEND;
    end else begin
      state <= next_state;
    end
  end
  
  // counter
  always_ff @(posedge clk) begin
    if (state == SEND) begin
      counter <= '0;
    end else begin
      counter <= counter + 1;
    end
  end

  // load n_cycles
  always_ff @(posedge clk) begin
    if (state == SEND) begin
      n_cycles <= cfg_drop_val ? cfg_drop_msg : n_cycles;
    end else begin
      n_cycles <= n_cycles;
    end
  end
  
endmodule
`endif