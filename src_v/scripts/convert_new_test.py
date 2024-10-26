import convert_new

module = """------------------------------------------------------------------------
// 2 Input Mux
//------------------------------------------------------------------------
module cmn_Mux2 #(
  parameter p_nbits = 1
) (
  input  logic [p_nbits-1:0] in0,
  in1,
  input  logic               sel,
  output logic [p_nbits-1:0] out
);

  always_comb begin
    case (sel)
      1'd0: out = in0;
      1'd1: out = in1;
      default: out = {p_nbits{1'bx}};
    endcase
  end

endmodule"""

module_content = module.split('\n')
# module_content = convert_new.clean_generate_block(module_content)
# module_content = convert_new.remove_duplicate_genvars(module_content)
module_content = convert_new.extract_module(module_content)
print("\n".join(module_content))

