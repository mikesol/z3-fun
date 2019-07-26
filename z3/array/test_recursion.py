from z3 import *
import pytest
from functools import reduce

@pytest.mark.skip # because too slow...
def test_cannot_handle_recursively_defined_array():
    a = Array('a', IntSort(), IntSort())
    s = Solver()
    x, y, c, d = Ints('x y c d')
    s.add(a[15] == 15)
    s.add(ForAll([x], Implies(x > 15, a[x] == a[x-1])))
    s.add(ForAll([y], Implies(y < 15, a[y] == a[y+1])))
    s.add(a[c] != 15)
    assert s.check() == unknown

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

def test_flattened_recursive_structure():
    '''
    It is possible to 
    '''
    MaybeInt = Datatype('MaybeInt')
    MaybeInt.declare('int', ('i', IntSort()))
    MaybeInt.declare('never')
    MaybeInt = MaybeInt.create()
    x = Const('x', MaybeInt)
    arr0 = Array('arr0', MaybeInt, MaybeInt)
    arr1 = Array('arr1', MaybeInt, MaybeInt)
    s = Solver()
    s.add(arr0 == Lambda([x],
        If(
            Or(x == MaybeInt.never, And(MaybeInt.is_int(x), MaybeInt.i(x) < 0)),
            MaybeInt.never,
            If(
                MaybeInt.i(x) == 0,
                MaybeInt.int(1),
                MaybeInt.int(MaybeInt.i(x) * MaybeInt.i(arr0[MaybeInt.int(MaybeInt.i(x) - 1)]))))))
    s.push()
    s.add(arr0[MaybeInt.int(5)] == MaybeInt.int(5 * 4  * 3 * 2 * 1))
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(arr0[MaybeInt.int(6)] == MaybeInt.int(5 * 4  * 3 * 2 * 1))
    assert s.check() == unsat
