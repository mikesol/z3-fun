from z3 import *

def test_or_not_implicit_and():
  '''
  Shows how s.add treats successive statements as And
  '''
  Tie, Shirt = Bools('Tie Shirt')
  s = Solver()
  s.add(Or(Tie, Shirt), 
      Or(Not(Tie), Shirt), 
      Or(Not(Tie), Not(Shirt)))
  assert s.check() == sat

def test_or_not_explicit_and():
  '''
  The same as test_or_not_implicit_and, but with an explicit And
  '''
  Tie, Shirt = Bools('Tie Shirt')
  s = Solver()
  s.add(And(And(Or(Tie, Shirt), 
      Or(Not(Tie), Shirt)), 
      Or(Not(Tie), Not(Shirt))))
  assert s.check() == sat