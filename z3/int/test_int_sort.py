from z3 import *

def test_int_sort():
    '''
    Int is a primitive Sort in Z3
    '''
    assert is_sort(IntSort())

def test_int_sort_sane():
    '''
    Int sort can be used in a function
    '''
    f = Function('f', IntSort(), IntSort())
    y, z = Ints('y z')
    s = Solver()
    s.add(f(y) == f(z))
    assert s.check() == sat

def test_int_sort_sane():
    '''
    Int sort will return unsat for nonsense functions
    '''
    f = Function('f', IntSort(), IntSort())
    y, z = Ints('y, z')
    s = Solver()
    s.add(f(y) == f(y + z))
    s.add(f(y) != f(y + z))
    assert s.check() == unsat