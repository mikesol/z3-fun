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

def test_groups_overlap():
  '''
  There exists a number that is between 1_8 but not in 4_12
  '''
  x = Int('x')
  in1_8 = And(x > 1, x < 8)
  in4_12 = And(x > 4, x < 12)
  s = Solver()
  s.add(in1_8)
  s.add(Not(in4_12))
  assert s.check() == sat
