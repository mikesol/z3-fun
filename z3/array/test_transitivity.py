from z3 import *

def test_transitive():
  binop = ArraySort(IntSort(), ArraySort(IntSort(), IntSort()))
  a, b = Consts('a b', binop)
  w, x, y, z = Ints('w x y z')
  s = Solver()
  s.add(a == Lambda(x, Lambda(y, x + y)))
  s.add(b == Lambda(w, Lambda(z, a[z][w])))
  s.push()
  s.add(a==b)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(a!=b)
  assert s.check() == unsat