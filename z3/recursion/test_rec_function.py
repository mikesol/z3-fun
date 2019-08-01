# RecFunction
# RecAddDefinition
from z3 import *

def test_recursive_function():
  fac = RecFunction('fac', IntSort(), IntSort())
  n = Int('n')
  RecAddDefinition(fac, n, If(n <= 0, 1, n*fac(n-1)))
  s = Solver()
  s.add(ForAll(n, fac(n) > 0))
  assert s.check() == unknown # s3 can't figure this out
  s.push()
  s.add(Exists(n, fac(n) < 1)) # interestingly, it *can* figure this out
  assert s.check() == unsat
  s.pop()
  s.push()
  s.add(Exists(n, fac(n) > 3)) # s3 can't figure this out 
  assert s.check() == unknown