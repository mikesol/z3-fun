from z3 import *
import pytest

def test_transitive():
  binop = ArraySort(IntSort(), ArraySort(IntSort(), IntSort()))
  a, b = Consts('a b', binop)
  w, x, y, z = Ints('w x y z')
  s = Solver()
  s.add(a == Lambda(x, Lambda(y, x + y)))
  s.add(b == Lambda(w, Lambda(z, a[z][w])))
  s.push()
  s.add(a == b)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(a != b)
  assert s.check() == unsat

@pytest.mark.skip
def test_not_transitive():
  binop = ArraySort(IntSort(), ArraySort(IntSort(), IntSort()))
  a, b = Consts('a b', binop)
  w, x, y, z = Ints('w x y z')
  s = Solver()
  s.add(a == Lambda(x, Lambda(y, x - y)))
  s.add(b == Lambda(w, Lambda(z, a[z][w])))
  #below is just as bad
  #s.add(ForAll([w,z], b[w][z] == a[z][w]))
  s.push()
  s.add(a != b)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(a == b)
  assert s.check() == unsat

def test_not_transitive2():
  a = Function('a', IntSort(), IntSort(), IntSort())
  b = Function('b', IntSort(), IntSort(), IntSort())
  w, x, y, z = Ints('w x y z')
  s = Solver()
  s.add(ForAll([x,y], a(x,y) == x - y))
  s.add(ForAll([w,z], b(w,z) == a(z, w)))
  s.push()
  s.add(a != b)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(a == b)
  assert s.check() == unsat

def test_not_transitive_with_existential_qualifier():
  binop = ArraySort(IntSort(), ArraySort(IntSort(), IntSort()))
  a, b = Consts('a b', binop)
  w, x, y, z = Ints('w x y z')
  s = Solver()
  s.add(a == Lambda(x, Lambda(y, x - y)))
  s.add(b == Lambda(w, Lambda(z, a[z][w])))
  s.push()
  s.add(Exists([x,y], a[x][y] != b[x][y]))
  assert s.check() == sat

def test_transitive_with_existential_qualifier():
  binop = ArraySort(IntSort(), ArraySort(IntSort(), IntSort()))
  a, b = Consts('a b', binop)
  w, x, y, z = Ints('w x y z')
  s = Solver()
  s.add(a == Lambda(x, Lambda(y, x + y)))
  s.add(b == Lambda(w, Lambda(z, a[z][w])))
  s.push()
  s.add(Exists([x,y], a[x][y] != b[x][y]))
  assert s.check() == unsat
  
