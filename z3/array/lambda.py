from z3 import *

def test_simple_lambda():
    '''
    Tests that if we define an array to function a certain way,
    it is unsatisfactory that it cannot work that way.
    '''
    z = Array('z', RealSort(), RealSort())
    i = Int('i')
    r = Real('r')
    s = Solver()
    s.add(Store(z, i, r) == Lambda([r], r + i)) # array is set to r + i
    s.add(Select(Store(z, i, r), i) != r + i) # we can never have a situation where it is *not* r + i
    assert s.check() == unsat


def test_simple_lambda_with_qualifier():
    '''
    If we qualify the lambda, then it works
    '''
    z = Array('z', RealSort(), RealSort())
    i = Int('i')
    r = Real('r')
    s = Solver()
    s.add(And(i > 0, Store(z, i, r) == Lambda([r], r + i))) # array is set to r + i for positive ints only
    s.add(Select(Store(z, i, r), i) != r + i) # we can have a situation where it is *not* r + i for negative ints
    assert s.check() == sat

def test_simple_lambda_with_overlapping_qualifier():
    '''
    If we qualify the lambda over the whole domain, then it doesn't work
    '''
    z = Array('z', RealSort(), RealSort())
    i = Int('i')
    r = Real('r')
    s = Solver()
    s.add(And(i > 0, Store(z, i, r) == Lambda([r], r + i))) # array is set to r + i for positive ints only
    s.add(And(i < 5, Store(z, i, r) == Lambda([r], r + i))) # array is set to r + i for positive ints only
    s.add(Select(Store(z, i, r), i) != r + i) # because i < 5 and i > 0 cover all ints, this will never hold
    assert s.check() == unsat