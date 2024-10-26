from pymtl3 import Interface, InPort, OutPort


# --------------------------------------------------------------------------
# SPI Interface
# --------------------------------------------------------------------------
class SPIMasterIfc(Interface):
    def construct(s, ncs):
        s.cs = [OutPort() for _ in range(ncs)]
        s.sclk = OutPort()
        s.mosi = OutPort()
        s.miso = InPort()

    def __str__(s):
        return f"{s.sclk}|{s.cs}|{s.mosi}|{s.miso}"


class SPIMinionIfc(Interface):
    def construct(s):
        s.sclk = InPort()
        s.cs = InPort()
        s.mosi = InPort()
        s.miso = OutPort()

    def __str__(s):
        return f"{s.sclk}|{s.cs}|{s.mosi}|{s.miso}"


# --------------------------------------------------------------------------
# Push Interface
# --------------------------------------------------------------------------
class PushOutIfc(Interface):

    def construct(s, Type):
        s.en = OutPort()
        s.msg = OutPort(Type)

        s.trace_len = len(f"{Type}")

    def __str__(s):
        if s.en:
            return f"{s.msg}"
        return " ".ljust(s.trace_len)


class PushInIfc(Interface):

    def construct(s, Type):
        s.en = InPort()
        s.msg = InPort(Type)

        s.trace_len = len(f"{Type}")

    def __str__(s):
        if s.en:
            return f"{s.msg}"
        return " ".ljust(s.trace_len)


# --------------------------------------------------------------------------
# Pull Interface
# --------------------------------------------------------------------------
class PullInIfc(Interface):

    def construct(s, Type):
        s.en = OutPort()
        s.msg = InPort(Type)

        s.trace_len = len(f"{Type}")

    def __str__(s):
        if s.en:
            return f"{s.msg}"
        return " ".ljust(s.trace_len)


class PullOutIfc(Interface):

    def construct(s, Type):
        s.en = InPort()
        s.msg = OutPort(Type)

        s.trace_len = len(f"{Type}")

    def __str__(s):
        if s.en:
            return f"{s.msg}"
        return " ".ljust(s.trace_len)
