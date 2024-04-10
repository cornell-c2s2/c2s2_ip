import pytest
from pymtl3 import *
from pymtl3.passes.backends.verilog import *
from pymtl3.stdlib.test_utils import run_sim
from pymtl3.stdlib import stream
from fixedpt import CFixed
from src.fixed_point.combinational.multi_butterfly import MultiButterflyWrapper
from src.fixed_point.sim import butterfly
import random
from tools.utils import mk_packed, mk_list_bitstruct, cfixed_bits
from src.fixed_point.utils import rand_fxp_spec, mk_butterfly_input, mk_butterfly_output


# Merge inputs into a single bus
def mk_msg(
    nbits: int, nsamples: int, a: list[CFixed], b: list[CFixed], w: list[CFixed]
):
    assert len(a) == nsamples
    assert len(b) == nsamples
    assert len(w) == nsamples

    inp_t = mk_butterfly_input(nbits)
    a = list(map(cfixed_bits, a))
    b = list(map(cfixed_bits, b))
    w = list(map(cfixed_bits, w))
    print(a, b, w)
    l = [inp_t(*a[i], *b[i], *w[i]) for i in range(nsamples)]
    print(l)
    return mk_list_bitstruct(inp_t, nsamples)(l)


# Merge outputs into a single bus
def mk_ret(nbits: int, nsamples: int, c: list[CFixed], d: list[CFixed]):
    assert len(c) == nsamples
    assert len(d) == nsamples
    out_t = mk_butterfly_output(nbits)
    c = list(map(cfixed_bits, c))
    d = list(map(cfixed_bits, d))
    l = [out_t(*c[i], *d[i]) for i in range(nsamples)]
    return mk_list_bitstruct(out_t, nsamples)(l)


# Create test parametrization information
# execution_number: number of times to run the test
# sequence_lengths: numbers of inputs to stream through the block
# n: bounds on number of bits in the fixed point number
# d: bounds on number of decimal bits in the fixed point number
# bin1: the butterfly parameter (b in 1 butterfly)
def mk_params(execution_number, sequence_lengths, n, d, bin1, slow=False):
    if isinstance(n, int):
        n = (n, n)
    if isinstance(d, int):
        d = (d, d)

    res = []

    for k in bin1:
        for j in range(execution_number):
            for i in sequence_lengths:
                res.append(
                    pytest.param(
                        j,  # execution_number index (unused)
                        i,  # number of inputs to stream
                        n,  # `n` bounds
                        d,  # `d` bounds
                        k,  # k in one butterfly
                        id=f"{i} ({n[0]}-{n[1]})-bit, ({d[0]}-{d[1]})-decimal-bit numbers"
                        + (f", {k}in1 butterfly "),
                        marks=pytest.mark.slow if slow else [],
                    )
                )
    return res


# Test harness for streaming data
class Harness(Component):
    def construct(s, n, d, b):
        s.dut = MultiButterflyWrapper(n, d, b)

        s.src = stream.SourceRTL(mk_list_bitstruct(mk_butterfly_input(n), b))
        s.sink = stream.SinkRTL(mk_list_bitstruct(mk_butterfly_output(n), b))

        s.src.send //= s.dut.recv
        s.dut.send //= s.sink.recv

    def done(s):
        return s.src.done() and s.sink.done()

    def line_trace(s):
        return (
            s.src.line_trace()
            + " > "
            + s.dut.line_trace()
            + " > "
            + s.sink.line_trace()
        )


# return a random fixed point value
def rand_cfixed(n, d):
    return CFixed(
        (random.randint(0, (1 << n) - 1), random.randint(0, (1 << n) - 1)),
        n,
        d,
        raw=True,
    )


@pytest.mark.skip(reason="Multi-butterfly harness broken")
@pytest.mark.parametrize(
    "n, d, a, b, w,",
    [
        (3, 0, (0, 1), (0, 1), (0, 1)),
        (2, 1, (1, 0), (1, 0), (1, 0)),
        (32, 16, (1, 0), (1, 0), (0, 0)),
        (8, 4, (1, 1), (1, 1), (1, 1)),
        (8, 4, (0.5, 0.5), (0.5, 0.5), (1, 0)),
        (6, 3, (3, 3), (3, 3), (1, 0)),  # overflow check
    ],
)
def test_edge(n, d, a, b, w):
    a = CFixed(a, n, d)
    b = CFixed(b, n, d)
    w = CFixed(w, n, d)

    model = Harness(n, d, 1)

    msg = []
    msg.append(mk_msg(n, 1, [a], [b], [w]))

    model.set_param(
        "top.src.construct",
        msgs=msg,
        initial_delay=0,
        interval_delay=0,
    )

    (c1, d1) = butterfly(a, b, w)

    ret = []
    ret.append(mk_ret(n, 1, [c1], [d1]))

    model.set_param(
        "top.sink.construct",
        msgs=ret,
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={"dump_textwave": False, "dump_vcd": "edge", "max_cycles": None},
        duts=["dut"],
    )

    # out = Fixed(int(eval_until_ready(model, a, b)), s, n, d, raw=True)

    # c = (a * b).resize(s, n, d)
    # print("%s * %s = %s, got %s" % (a.bin(dot=True), b.bin(dot=True), c.bin(dot=True), out.bin(dot=True)))
    # assert c.bin() == out.bin()


def concat_Bits(list, n):
    res = list[0]
    for i in range(1, len(list)):
        res = concat(res, list[i])
    return res


@pytest.mark.skip(reason="Multi-butterfly harness broken")
@pytest.mark.parametrize(
    "execution_number, sequence_length, n, d, bin1",
    # Runs tests on smaller number sizes
    mk_params(50, [1, 50], (2, 8), (0, 8), bin1=[1, 2, 16], slow=True) +
    # Runs tests on 20 randomly sized fixed point numbers, inputting 1, 5, and 50 numbers to the stream
    mk_params(20, [1, 100], (16, 32), (0, 32), bin1=[1, 2, 4], slow=True) +
    # Extensively tests numbers with certain important bit sizes.
    sum(
        [
            [
                *mk_params(1, [20], n, d, [1, 2, 4, 16], slow=False),
                *mk_params(1, [1000], n, d, [1, 2, 4], slow=True),
            ]
            for (n, d) in [(8, 4), (24, 8), (32, 24), (32, 16)]
        ],
        [],
    ),
)
def test_random(
    cmdline_opts, execution_number, sequence_length, n, d, bin1
):  # test individual and sequential multiplications to assure stream system works
    random.seed(random.random() + execution_number)
    n, d = rand_fxp_spec(n, d)

    dat = []
    solns = []
    for i in range(sequence_length):
        input = []
        output = []
        for j in range(bin1):
            a = rand_cfixed(n, d)
            b = rand_cfixed(n, d)
            w = rand_cfixed(n, d)
            input.append(mk_msg(n, bin1, a, b, w))
            c, dd = butterfly(a, b, w)
            output.append(mk_ret(n, c.get(), dd.get()))

        dat.append(concat_Bits(input, n * 6))
        solns.append(concat_Bits(output, n * 4))

    model = Harness(n, d, bin1)

    model.set_param("top.src.construct", msgs=dat, initial_delay=0, interval_delay=0)

    model.set_param(
        "top.sink.construct",
        msgs=solns,
        initial_delay=0,
        interval_delay=0,
    )

    run_sim(
        model,
        cmdline_opts={
            **cmdline_opts,
            "max_cycles": (
                300 + 30 + ((n + 2) * 3 + 4) * len(dat)
            ),  # makes sure the time taken grows linearly with respect to n
        },
        duts=["dut"],
    )
