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
  arr = Const('arr', SetSort(IntSort()))
  a = Int(str(uuid4()))
  npv = pv + [a]
  s.add(arr == st)
  s.add(And(*[arr[x] for x in npv]))
  s.add(Distinct(*npv))
  if s.check() != unsat:
    return rec(st, npv, a + running_sum, l + 1)
  else:
    return running_sum, pv

# looks like we need to add equality constraints for eevvrrrrythiinng
# then tried to get clever with at least, didn't work...
#@pytest.mark.skip
def test_reduce_on_set_0():
  ssis = SetSort(IntSort())
  arr = Const('arr', SetSort(IntSort()))
  lam = EmptySet(IntSort())
  s = Solver()
  sm, pv = rec(lam, [], 0, 0)
  s.add(arr == lam)
  if len(pv) > 0:
    s.add(And(*[arr[x] for x in pv]))
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
  arr = Const('arr', SetSort(IntSort()))
  i = Int('i')
  lam = Lambda(i, And(i < 5, i >= 0))
  s = Solver()
  sm, pv = rec(lam, [], 0, 0)
  s.add(arr == lam)
  s.add(And(*[arr[x] for x in pv]))
  s.add(Distinct(*pv))
  s.push()
  s.add(sm == 11)
  s.check()
  assert s.check() == unsat
  s.pop()
  s.push()
  s.add(sm == 10)
  assert s.check() == sat

def test_reduce_with_loop():
  s = Solver()
  i = Int('i')
  arr = Array('arr', IntSort(), BoolSort())
  s.add(arr == Lambda(i, And(i < 5, i >= 0)))
  sm = 0
  while True:
    f = Int(str(uuid4()))
    s.push()
    s.add(arr[f])
    if s.check() == unsat:
      s.pop()
      break
    s.pop()
    s.add(arr[f])
    sm = f + sm
    arr = SetDel(arr, f)
  s.push()
  s.add(sm == 10)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(sm == 11)
  assert s.check() == unsat

def test_reduce_with_loop_model():
  s = Solver()
  i = Int('i')
  arr = Array('arr', IntSort(), BoolSort())
  LIM = 10
  s.add(arr == Lambda(i, And(i < LIM, i >= 0)))
  sm = 0
  f = Int(str(uuid4()))
  while True:
    s.push()
    s.add(arr[f])
    chk = s.check()
    if chk == unsat:
      s.pop()
      break
    tmp = s.model()[f]
    sm = sm + tmp
    s.pop()
    s.add(f != tmp)
  s.push()
  s.add(sm == sum(range(LIM)))
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(sm == 11)
  assert s.check() == unsat

def test_reduce_f_with_loop():
  s = Solver()
  i = Int('i')
  fun = Function('fun', IntSort(), BoolSort())
  s.add(ForAll(i, fun(i) == And(i < 4, i >= 0)))
  sm = 0
  while True:
    f = Int(str(uuid4()))
    s.push()
    s.add(fun(f))
    if s.check() == unsat:
      s.pop()
      break
    s.pop()
    s.add(fun(f))
    sm = f + sm
    _F = Function(str(uuid4()), IntSort(), BoolSort())
    s.add(ForAll(i, _F(i) == If(i == f, False, fun(i))))
    fun = _F
  s.push()
  s.add(sm == 6)
  assert s.check() == sat
  s.pop()
  s.push()
  s.add(sm == 11)
  assert s.check() == unsat

# why doesn't this work
@pytest.mark.skip
def test_reduce_with_recur_f():
  LIM = 5
  VARS = 10
  poss = [Int('i%d'%x) for x in range(VARS)]
  i = Int('i')
  s = Solver()
  arr = Array('arr', IntSort(), BoolSort())
  s.add(arr == Lambda(i, And(i < LIM, i >= 0)))
  a = arr
  for x in range(1,len(poss)):
    s.add(poss[x-1] != poss[x])
  for x in range(len(poss)):
    s.add(Implies(a != EmptySet(IntSort()), arr[poss[x]]))
    a = SetDel(a, poss[x])
  def final_stmt(l):
    if len(l) == 0: return 0
    return If(Not(arr[l[0]]), 0, l[0] + (0 if len(l) == 1 else final_stmt(l[1:])))
  sm = final_stmt(poss)
  s.push()
  s.add(sm == 1)
  assert s.check() == unsat

def test_reduce_with_known_entities():
  LIM = 20
  VARS = 25
  poss = [Int('i%d'%x) for x in range(VARS)]
  i = Int('i')
  s = Solver()
  arr = EmptySet(IntSort())
  for x in range(LIM):
    arr = Store(arr, x, True)
  a = arr
  for x in range(1,len(poss)):
    s.add(poss[x-1] != poss[x])
  for x in range(len(poss)):
    s.add(Implies(a != EmptySet(IntSort()), arr[poss[x]]))
    a = SetDel(a, poss[x])
  def final_stmt(l):
    if len(l) == 0: return 0
    return If(Not(arr[l[0]]), 0, l[0] + (0 if len(l) == 1 else final_stmt(l[1:])))
  sm = final_stmt(poss)
  s.push()
  s.add(sm == 1)
  assert s.check() == unsat
  s.pop()
  s.push()
  s.add(sm == sum(range(LIM)))
  assert s.check() == sat
