from z3 import *
import pytest
from uuid import uuid4

'''
F
f(x) union g(x) == x
f(x) intersection g(x) == emptyset
f(x) != emptyset
if g(x) == emptyset 1
'''

@pytest.mark.skip
def test_reduce_on_set():
  # does not work, keeps getting unknowns
  ssis = SetSort(IntSort())
  f = Function('f', ssis, ssis)
  g = Function('g', ssis, ssis)
  c, d = Consts('c d', ssis)
  i = Int('i')
  s = Solver()
  esi = EmptySet(IntSort())
  fsi = FullSet(IntSort())
  assert s.check() == sat
  s.add(ForAll(c, SetUnion(f(c), g(c)) == c))
  s.add(ForAll(c, SetIntersect(f(c), g(c)) == esi))
  s.add(ForAll(c, Implies(c != esi, f(c) != esi)))
  s.add(ForAll([c, i], Implies(And(f(c) != esi, f(c) != Store(esi, i, True)), g(c) != esi)))
  assert s.check() == sat
  a = Array('a', ssis, IntSort())
  x = Const('x', ssis)
  s.add(a == Lambda(x, If(g(x) == esi, 1, a[f(x)] + a[g(x)])))
  assert s.check() == sat
  s.push()
  s.add(a[esi] == 0)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(a[esi] == 1)
  assert s.check() == unsat

@pytest.mark.skip
def test_other_strategy_reduce_on_set():
  # does not work, keeps getting unknowns
  ssis = SetSort(IntSort())
  f = Array('f', ssis, ssis)
  g = Array('g', ssis, ssis)
  c, d, e = Consts('c d e', ssis)
  s = Solver()
  esi = EmptySet(IntSort())
  fsi = FullSet(IntSort())
  assert s.check() == sat
  s.add(f == Lambda(c,
    If(c == esi,
      c,
      If(Exists(d, And(IsSubset(d, c), d != EmptySet(IntSort()), d != c)),
        SetDifference(c, g[c]),
        c))))
  s.add(g == Lambda(e, SetDifference(e, f[e])))
  assert s.check() == sat
  a = Array('a', ssis, IntSort())
  x = Const('x', ssis)
  s.add(a == Lambda(x, If(g(x) == esi, 1, a[f(x)] + a[g(x)])))
  assert s.check() == sat
  s.push()
  s.add(a[esi] == 0)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(a[esi] == 1)
  assert s.check() == unsat



def rec(st, pv, running_sum, l):
  if (l == 1000):
    return
  s = Solver()
  gg = Const('gg', SetSort(IntSort()))
  a = Int(str(uuid4()))
  npv = pv + [a]
  s.add(gg == st)
  s.add(And(*[gg[x] for x in npv]))
  s.add(Distinct(*npv))
  if s.check() != unsat:
    return rec(st, npv, a + running_sum, l + 1)
  else:
    return running_sum, pv

# looks like we need to add equality constraints for eevvrrrrythiinnggg
# then tried to get clever with at least, didn't work...
#@pytest.mark.skip
def test_reduce_on_set_0():
  ssis = SetSort(IntSort())
  gg = Const('gg', SetSort(IntSort()))
  lam = EmptySet(IntSort())
  s = Solver()
  sm, pv = rec(lam, [], 0, 0)
  s.add(gg == lam)
  if len(pv) > 0:
    s.add(And(*[gg[x] for x in pv]))
    s.add(Distinct(*pv))
  assert s.check() == sat
  s.push()
  s.add(sm == 0)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(sm == 1)
  assert s.check() == unsat

#@pytest.mark.skip
# this only really works with a size less than 5
# otherwise it hangs
def test_reduce_on_set_1():
  ssis = SetSort(IntSort())
  s = Solver()
  gg = Const('gg', SetSort(IntSort()))
  i = Int('i')
  lam = Lambda(i, And(i < 5, i >= 0))
  s = Solver()
  sm, pv = rec(lam, [], 0, 0)
  s.add(gg == lam)
  s.add(And(*[gg[x] for x in pv]))
  s.add(Distinct(*pv))
  s.push()
  s.add(sm == 11)
  s.check()
  assert s.check() == unsat
  s.pop()
  s.push()
  s.add(sm == 10)
  assert s.check() == sat