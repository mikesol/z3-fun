from z3 import *

def test_real_sort():
    '''
    Real is a primitive Sort in Z3
    '''
    assert is_sort(RealSort())

def test_real_sort_sane():
    '''
    Real sort can be used in a function
    '''
    f = Function('f', RealSort(), RealSort())
    y, z = Reals('y z')
    s = Solver()
    s.add(f(y) == f(z))
    assert s.check() == sat

def test_real_sort_sane():
    '''
    Real sort will return unsat for nonsense functions
    '''
    f = Function('f', RealSort(), RealSort())
    y, z = Reals('y, z')
    s = Solver()
    s.add(f(y) == f(y + z))
    s.add(f(y) != f(y + z))
    assert s.check() == unsat