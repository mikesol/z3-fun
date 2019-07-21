from z3 import *
import pytest

def test_func_elim_array_store():
  '''
  Shows how store returns a new array with the stored object
  Shows how select selects an object
  Shows how indices to arrays can be compared to ints
  '''
  Z = IntSort()
  f = Function('f', Z, Z)
  x, y, z = Ints('x y z')
  A = Array('A', Z, Z)
  s = Solver()
  s.add(x + 2 == y) # x + 2 must be y
  '''
  functions should be stripped
  we return a new array where 3 is stored at x and index [y-2], which should be x
  y - x + 1 is 3, so the two should be equal
  '''
  s.add(f(Store(A, x, 3)[y - 2]) == f(y - x + 1))
  assert s.check() == sat
  s = Solver()
  s.add(x + 2 == y)
  s.add(f(Store(A, x, 3)[y - 2]) != f(y - x + 1)) # same as above, but let's make not eq
  assert s.check() == unsat