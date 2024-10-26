# =========================================================================
# wishbone
# =========================================================================

from os import path
from pymtl3 import *
from pymtl3.passes.backends.verilog import *


class Wishbone(VerilogPlaceholder, Component):
    def construct(s, p_num_msgs=4, p_num_istream=3, p_num_ostream=3):

        s.c_addr_nbits = clog2(p_num_msgs)
        s.istream_addr_nbits = clog2(p_num_istream)
        s.ostream_addr_nbits = clog2(p_num_ostream)

        s.wbs_stb_i = InPort(1)
        s.wbs_cyc_i = InPort(1)
        s.wbs_we_i = InPort()
        s.wbs_sel_i = InPort(4)
        s.wbs_dat_i = InPort(32)
        s.wbs_adr_i = InPort(32)
        s.wbs_ack_o = OutPort(1)
        s.wbs_dat_o = OutPort(32)

        s.istream_rdy = [InPort(1) for _ in range((p_num_istream))]
        s.istream_val = [OutPort(1) for _ in range((p_num_istream))]

        s.ostream_rdy = [OutPort(1) for _ in range((p_num_ostream))]
        s.ostream_val = [InPort(1) for _ in range((p_num_ostream))]

        s.ostream_data = [InPort(32) for _ in range((p_num_istream))]
        s.istream_data = [OutPort(32) for _ in range((p_num_ostream))]

        # Source file path
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "wishbone.v"),
        )
