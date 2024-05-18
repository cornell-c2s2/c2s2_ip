# Creates a stateful crossbar.
# Provides a function to configure the crossbar as well
# as a function to pass inputs through the crossbar.
def create_crossbar(nbits: int, nin: int, nout: int) -> tuple[callable, callable]:
    in_sel = 0
    out_sel = 0

    def crossbar(inp: list[any]):
        outputs = [0 for _ in range(nout)]
        outputs[out_sel] = inp[in_sel]
        # All outputs are zero except for the selected output
        return outputs

    def configure(_in_sel: int, _out_sel: int):
        nonlocal in_sel, out_sel
        in_sel = _in_sel
        out_sel = _out_sel

    return crossbar, configure
