// Calculate the sum of an array of numbers
// The width of the array must be a power of 2.
// Sums recursively to minimize the critical path
module classifier_helpers_Sum #(
  parameter int BIT_WIDTH = 32,
  parameter int N_SAMPLES = 8
) (
  input logic clk,
  input logic reset,
  input logic [BIT_WIDTH-1:0] arr[N_SAMPLES-1:0],
  output logic [BIT_WIDTH-1:0] sum
);

  generate
    if (N_SAMPLES == 1) begin : base_case
      // Base case
      // If the array has only one element, the sum is the element itself
      // This is the base case of the recursion
      assign sum = arr[0];
    end else begin
      // Recursive case
      // Split the array in half and sum the two halves
      logic [BIT_WIDTH-1:0] left;
      logic [BIT_WIDTH-1:0] right;

      classifier_helpers_Sum #(
        .BIT_WIDTH(BIT_WIDTH),
        .N_SAMPLES(N_SAMPLES / 2)
      ) left_sum (
        .clk  (clk),
        .reset(reset),
        .arr  (arr[N_SAMPLES/2-1:0]),
        .sum  (left)
      );

      classifier_helpers_Sum #(
        .BIT_WIDTH(BIT_WIDTH),
        .N_SAMPLES(N_SAMPLES / 2)
      ) right_sum (
        .clk  (clk),
        .reset(reset),
        .arr  (arr[N_SAMPLES-1:N_SAMPLES/2]),
        .sum  (right)
      );

      // The sum of the array is the sum of the left half plus the sum of the right half
      assign sum = left + right;
    end
  endgenerate

endmodule
