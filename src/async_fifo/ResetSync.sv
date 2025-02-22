`ifndef BRGTC6_RESET_SYNC
`define BRGTC6_RESET_SYNC

//=========================================================================
// Reset Synchronizer Implementation
//=========================================================================
module ResetSync (
    input  logic  clk,
    input  logic  async_rst,
    output logic  reset
);

logic reg1;
logic reg2;

always @(posedge clk or posedge async_rst) begin
    if (async_rst) begin
        reg1 <= 1'b1;
        reg2 <= 1'b1;
    end else begin
        reg1 <= 1'b0;
        reg2 <= reg1;
    end
end

assign reset = reg2;

endmodule

`endif /* BRGTC6_RESET_SYNC */
