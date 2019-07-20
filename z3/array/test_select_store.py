from z3 import *

def test_composite_data_structure():
  # int < 5 is subset of int < 5 & real < 6, but not other way around
  Foobar = Datatype('Foobar')
  Foobar.declare('int', ('i', IntSort()))
  Foobar.declare('real', ('r', RealSort()))
  Foobar = Foobar.create()
  arr0 = Array('arr0', Foobar, BoolSort())
  arr1 = Array('arr1', Foobar, BoolSort())
  x, xx = Ints('x xx')
  y, yy = Reals('y yy')
  s = Solver()
  fff = Int('fff')
  aaa = Array('aaa', IntSort(), IntSort())
  assert is_const(fff)
  assert is_app(x)
  assert is_const(x)
  s.add(ForAll([fff], aaa[fff] == False))
  s.add(ForAll([x], Implies(x < 0, arr0[Foobar.int(x)] == False)))
  #s.add(ForAll([y], arr0[Foobar.real(y)] == False))
  s.add(ForAll([xx], Implies(xx < 0, arr1[Foobar.int(xx)] == False)))
  #s.add(ForAll([yy], arr1[Foobar.real(yy)] == True))
  s.add(IsSubset(arr0, arr1))
  assert s.check() == sat


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