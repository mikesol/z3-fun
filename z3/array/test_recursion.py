from z3 import *
import pytest
from functools import reduce


def test_faux_recursive_function():
    to15 = RecFunction('to15', IntSort(), IntSort())
    i, x, y = Ints('i x y')
    arr0 = Array('arr0', IntSort(), IntSort())
    TARGET = 12 # anything larger hangs a long time
    to15 = lambda m, n: 15 if n == TARGET else If(m == 15, m, to15(m + If(m > 15, -1, 1), n + 1))
    lamb = Lambda([i], to15(i, 0))
    s = Solver()
    s.add(arr0 == lamb)
    s.add(arr0[x] != 15)
    assert s.check() == unsat