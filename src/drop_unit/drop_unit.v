//================================================
// drop_unit.v
//================================================
`default_nettype none
`ifndef DROP_UNIT_V
`define DROP_UNIT_V

module drop_unit #(
  parameter int n_bits = 8,
  parameter int max_n_cycles = 10  // The number of cycles the unit waits for before sending a sample
) (
  // Clock and Reset Ports
  input  logic  clk,
  input  logic  reset,
  input  logic  enable,                // If 1, disable drop unit (send every req_msg to resp_msg). In this mode, the drop unit acts basically like a wire.
 
  input  logic [n_bits-1:0]            req_msg,
  input  logic                         req_val,
  output logic                         req_rdy,
 
  output  logic [n_bits-1:0]           resp_msg,
  output  logic                        resp_val,
  input logic                          resp_rdy,
 
  input logic    [max_n_cycles-1:0]    cfg_drop_msg, // A counter value to denote the number of cycles between captured samples.
  input logic                          cfg_drop_val,  // Val signal for above
  output logic                         cfg_drop_rdy
);

  localparam IDLE = 2'd0, SEND = 2'd1, DROP = 2'd2;
  logic [1:0] state, next_state;
  
  logic [$clog2(max_n_cycles)-1:0] n_cycles;
  logic [$clog2(max_n_cycles)-1:0] counter;

  // manage state
  always_comb begin
    case (state)
      IDLE: begin
        if (req_val == 1) begin
          next_state = SEND;
        end else begin
          next_state = IDLE;
        end
      end
      SEND: begin
        if (enable == 0) begin
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
        next_state = IDLE;
      end
    endcase
  end

  // manage data path
  always_comb begin
    case (state)
      IDLE: begin
        req_rdy = 0;
        resp_msg = '0;
        resp_val = 0;
        cfg_drop_rdy = 1;
      end
      SEND: begin
        req_rdy = 1;
        resp_msg = req_msg;
        resp_val = 1;
        cfg_drop_rdy = 0;
      end
      DROP: begin
        req_rdy = 1;
        resp_msg = 0;
        resp_val = 0;
        cfg_drop_rdy = 0;
      end
      default: begin
      end
    endcase
  end

  // reset logic
  always_ff @(posedge clk) begin
    if (reset) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end
  
  // counter
  always_ff @(posedge clk) begin
    if (state == IDLE || state == SEND) begin
      counter <= '0;
    end else begin
      counter <= counter + 1;
    end
  end

  // load n_cycles
  always_ff @(posedge clk) begin
    if (state == IDLE) begin
      n_cycles <= cfg_drop_val ? cfg_drop_msg : max_n_cycles;
    end else begin
      n_cycles <= n_cycles;
    end
  end
  
endmodule
`endif