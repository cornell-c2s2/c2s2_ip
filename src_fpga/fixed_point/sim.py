from fixedpt import CFixed, Fixed

# Exact simulation of all the fixed point hardware


# Fixed point addition
def add(a: Fixed, b: Fixed) -> Fixed:
    assert a._n == b._n
    assert a._d == b._d
    return (a + b).resize(None, a._n, a._d)


# Fixed point multiplication
def multiply(a: Fixed, b: Fixed) -> Fixed:
    assert a._n == b._n
    assert a._d == b._d
    return (a * b).resize(None, a._n, a._d)


# Complex multiplication with fixed precision
# Uses the gaussian formula to multiply two complex numbers
def complex_multiply(a: CFixed, b: CFixed) -> CFixed:
    assert a.real._n == b.real._n
    assert a.real._d == b.real._d
    n = a.real._n
    d = a.real._d

    ac = multiply(a.real, b.real)
    bc = multiply(a.imag, b.imag)

    c = multiply(add(a.real, a.imag), add(b.real, b.imag))

    return CFixed.cast((ac - bc, c - ac - bc)).resize(n, d)


# Performs the butterfly operation on two complex numbers
# Used to generate the expected output
def butterfly(a: CFixed, b: CFixed, w: CFixed) -> tuple[CFixed, CFixed]:
    assert a.real._n == b.real._n
    assert a.real._d == b.real._d
    assert a.real._n == w.real._n
    assert a.real._d == w.real._d

    n = a.real._n
    d = a.real._d

    t = complex_multiply(b, w)
    return ((a + t).resize(n, d), (a - t).resize(n, d))
