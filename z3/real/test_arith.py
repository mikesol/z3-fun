from z3 import *

def test_roots():
  '''
  The roots of two polynomials do not overlap
  '''
  x = Real('x')
  root_eq_0 = (x**5) - (4*(x**4)) + (2*(x**3)) - (7*x) + 3 == 0
  root_eq_1 = (12*(x**4)) - (3*(x**2)) + x == 0
  s = Solver()
  s.add(root_eq_0)
  s.add(Not(root_eq_1))
  assert s.check() == sat

def test_roots():
  '''
  The roots of two polynomials overlap completely
  '''
  x = Real('x')
  root_eq_0 = (x**5) - (4/5*(x**4)) + (2*(x**3)) - (7*x) + 3 == 0
  root_eq_1 = (x**6) - (4/5*(x**5)) + (2*(x**4)) - (7*(x**2)) + (3*x) == 0
  s = Solver()
  s.add(root_eq_0)
  s.add(Not(root_eq_1))
  assert s.check() == unsat

def test_sqrt():
    '''
    Cannot handle square root equality
    '''
    x = Real('x')
    s = Solver()
    s.add(Sqrt(x) == x)
    assert s.check() == unknown