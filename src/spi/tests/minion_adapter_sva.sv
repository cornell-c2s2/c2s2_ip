`include "spi/helpers/minion_adapter.v"


module spi_helpers_Minion_Adapter_sva #(
  parameter int nbits = 8,
  parameter int num_entries = 1
) (
  input logic             clk,
  input logic             reset,
  input logic             pull_en,
  input logic             pull_msg_val,
  input logic             pull_msg_spc,
  input logic [nbits-3:0] pull_msg_data,
  input logic             push_en,
  input logic             push_msg_val_wrt,  // write mode
  input logic             push_msg_val_rd,   // read mode
  input logic [nbits-3:0] push_msg_data,
  input logic [nbits-3:0] recv_msg,
  input logic             recv_rdy,
  input logic             recv_val,
  input logic [nbits-3:0] send_msg,
  input logic             send_rdy,
  input logic             send_val,
  input logic             parity
);


// WHITEBOX PROPERTIES (CHECKS INTERNAL CONTROL LOGIC)

// checks that master to chip and chip to master don't overflow

// for the master to chip queue
// master to chip queue
assign mc_q_recv_rdy = spi_helpers_Minion_Adapter.mc_q_recv_rdy;
assign mc_q_recv_val = spi_helpers_Minion_Adapter.mc_q_recv_val;
reg [3:0] msg_cnt_mc;  // Message counter for Master-to-Chip queue

always_ff @(posedge clk) begin: count_messages_mc
    if (reset) begin
        msg_cnt_mc <= 4'b0;
    end else begin
        // Track enqueue and dequeue activity
        case ({mc_q_recv_rdy && mc_q_recv_val, send_rdy && send_val}) // {read, write}
            2'b10: msg_cnt_mc <= msg_cnt_mc + 1; // Enqueue
            2'b01: msg_cnt_mc <= msg_cnt_mc - 1; // Dequeue
            default: msg_cnt_mc <= msg_cnt_mc;   // No change or simultaneous enqueue/dequeue
        endcase
    end
end

// property to detect overflow in the master-to-chip queue
property no_queue_overflow_mc;
    @(posedge clk) disable iff (reset) (msg_cnt_mc <= num_entries);
endproperty

// assertion for the master-to-chip queue
MC_QUEUE_OFLOW : assert property (no_queue_overflow_mc);

// property to detect underflow in the master-to-chip queue
property no_queue_underflow_mc;
    @(posedge clk) disable iff (reset) (msg_cnt_mc >= 0);
endproperty

// assertion for the master-to-chip queue underflow
MC_QUEUE_UFLOW : assert property (no_queue_underflow_mc);


// chip to master queue

assign cm_q_send_rdy = spi_helpers_Minion_Adapter.cm_q_send_rdy;
assign cm_q_send_val = spi_helpers_Minion_Adapter.cm_q_send_val;
reg [3:0] msg_cnt_cm;  // message counter for chip-to-master queue

always_ff @(posedge clk) begin: count_messages_cm
    if (reset) begin
        msg_cnt_cm <= 4'b0;
    end else begin
        // track enqueue and dequeue activity
        case ({recv_rdy && recv_val, cm_q_send_rdy && cm_q_send_val})
            2'b10: msg_cnt_cm <= msg_cnt_cm + 1; // enqueue
            2'b01: msg_cnt_cm <= msg_cnt_cm - 1; // dequeue
            default: msg_cnt_cm <= msg_cnt_cm;   // no change
        endcase
    end
end

// property to detect overflow in the chip-to-master queue
property no_queue_overflow_cm;
    @(posedge clk) disable iff (reset) (msg_cnt_cm <= num_entries);
endproperty

// assertion for the chip-to-master queue
CM_QUEUE_OFLOW : assert property (no_queue_overflow_cm);

// property to detect underflow in the chip-to-master queue
property no_queue_underflow_cm;
    @(posedge clk) disable iff (reset) (msg_cnt_cm >= 0);
endproperty

// assertion for the chip-to-master queue underflow
CM_QUEUE_UFLOW : assert property (no_queue_underflow_cm);


// BLACKBOX TESTS (CHECKS INPUT --> OUTPUT MATCHES SPEC)

// checks that for every push there is a corresponding send
property push_to_send;
  @(posedge clk) disable iff (reset)
    (push_msg_val_wrt && push_en) |-> ##[0:$] (send_val);
endproperty

PUSH_TO_SEND : assert property (push_to_send);

// checks that for every recv there is a corresponding push
property send_to_push;
    @(posedge clk) disable iff(reset)
     (push_msg_val_rd && pull_en && recv_val && recv_rdy) |-> ##[0:$] (cm_q_send_val); // discrepency from diagram: pull_msg_val = cm_q_send_rdy & cm_q_send_val
endproperty
SEND_TO_PUSH : assert property (send_to_push);

// message parity checks
// checks that the message pushed is the same as the message sent
reg [nbits-3:0] pushed_msg;
reg push_matches_send;
always_ff @(posedge clk) begin: compare_push_send
    if (reset)
    if (push_msg_val_wrt && push_en) begin
      pushed_msg = push_msg_data;
    end
    if (send_val) begin
      push_matches_send <= (pushed_msg == send_msg);
    end
end

property push_to_send_msg;
    @(posedge clk) disable iff(reset)
      (push_msg_val_rd && pull_en && recv_val && recv_rdy) |-> ##[0:$] (push_matches_send);
endproperty

PUSH_TO_SEND_PARITY : assert property (push_to_send_msg);

// val/rdy checks


// push/pull checks

endmodule
bind spi_helpers_Minion_Adapter spi_helpers_Minion_Adapter_sva tb(.*);
