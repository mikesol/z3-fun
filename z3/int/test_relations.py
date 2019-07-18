from z3 import *

def test_g7_must_be_g5():
  '''
  Shows how an impossible relation (x > 5 & !(x > 7)) will fail
  '''
  x = Int('x')
  gt5 = x > 5
  gt7 = x > 7
  s = Solver()
  s.add(gt7) # it is greater than 7
  s.add(Not(gt5)) # ...but not greater than 5 ?!?!?
  assert s.check() == unsat # should be unsat