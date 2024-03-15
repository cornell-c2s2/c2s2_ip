from pymtl3 import *
from pymtl3.stdlib import stream
from pymtl3.passes.backends.verilog import *
from os import path
from src.serdes.deserializer import Deserializer
from src.serdes.serializer import Serializer

# Pymtl3 harness for the `Classifier` module.
class Classifier(VerilogPlaceholder, Component):
    # Constructor

    def construct(s, BIT_WIDTH=32, DECIMAL_PT = 16, N_SAMPLES = 8, CUTOFF_FREQ = 65536000, CUTOFF_MAG = 1310720, SAMPLING_FREQUENCY = 44000):
        # Interface
        s.recv_msg = [InPort(BIT_WIDTH) for _ in range(N_SAMPLES)]
        s.recv_val = InPort()
        s.recv_rdy = OutPort()

        s.send_msg = OutPort()
        s.send_val = OutPort()
        s.send_rdy = InPort()

        s.set_metadata(VerilogPlaceholderPass.top_module, "Classifier")
        s.set_metadata(
            VerilogPlaceholderPass.src_file,
            path.join(path.dirname(__file__), "classifier.v"),
        )

class ClassifierWrapper(Component):
    def construct(s, BIT_WIDTH, DECIMAL_PT, N_SAMPLES, CUTOFF_FREQ, CUTOFF_MAG, SAMPLING_FREQUENCY):
        s.recv = stream.ifcs.RecvIfcRTL(mk_bits(BIT_WIDTH))
        s.send = stream.ifcs.SendIfcRTL(mk_bits(1))

        # Hook up a deserializer
        s.deserializer = Deserializer(BIT_WIDTH, N_SAMPLES)
        s.recv.msg //= s.deserializer.recv_msg
        s.recv.val //= s.deserializer.recv_val
        s.deserializer.recv_rdy //= s.recv.rdy

        # Hook up classifier
        s.dut = Classifier(BIT_WIDTH, DECIMAL_PT, N_SAMPLES, CUTOFF_FREQ, CUTOFF_MAG, SAMPLING_FREQUENCY)

        s.dut.send_msg //= s.send.msg
        s.dut.send_val //= s.send.val
        s.send.rdy //= s.dut.send_rdy

        # Hook up the deserializer to the Classifier
        for i in range(N_SAMPLES):
            s.deserializer.send_msg[i] //= s.dut.recv_msg[i]

        s.deserializer.send_val //= s.dut.recv_val
        s.dut.recv_rdy //= s.deserializer.send_rdy

    def line_trace(s):
        return f"{s.deserializer.line_trace()} > {s.dut.line_trace()}"