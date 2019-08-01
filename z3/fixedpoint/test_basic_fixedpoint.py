from z3 import *
import pytest

def test_fp_hello_world():
  fp = Fixedpoint()
  a, b, c = Bools('a b c')
  fp.register_relation(a.decl(), b.decl(), c.decl()) # declares relation to engine
  fp.rule(a, b)
  fp.rule(b, c)
  fp.set(engine='datalog')
  # a follows from b
  # b follow from c
  # but as we have not established c, we cannot establish b
  assert fp.query(a) == unsat
  assert fp.query(b) == unsat
  fp.fact(c) # same as fp.rule(c, True)
  assert fp.query(a) == sat
  assert fp.query(b) == sat


# basic fixed point is only possible over finite types like bit vectors
def test_fp_ordering1():
  fp = Fixedpoint()
  fp.set(engine='datalog')
  bvs = BitVecSort(16)
  a, b, c =  BitVecs('a b c', 16)
  d = BitVecVal(10, 16)
  e = BitVecVal(11, 16)
  f = BitVecVal(12, 16)
  g = BitVecVal(13, 16)
  h = BitVecVal(14, 16)
  my_rel = Function('my_rel', bvs, bvs, BoolSort())
  fp.register_relation(my_rel)
  fp.declare_var(a, b, c)
  fp.rule(my_rel(a, c), [my_rel(a, b), my_rel(b, c)])
  assert fp.query(my_rel(d, h)) == unsat
  fp.fact(my_rel(d, e))
  fp.fact(my_rel(e, f))
  #fp.fact(my_rel(f, g))
  fp.fact(my_rel(g, h))
  assert fp.query(my_rel(d, h)) == unsat
  fp.fact(my_rel(f, g))
  assert fp.query(my_rel(d, h)) == sat

def test_mccarthy_91():
  mc = Function('mc', IntSort(), IntSort(), BoolSort())
  n, m, p = Ints('n m p')

  fp = Fixedpoint()

  fp.declare_var(n,m,p)
  fp.register_relation(mc)

  fp.rule(mc(m, m-10), m > 100)
  fp.rule(mc(m, n), [m <= 100, mc(m+11,p), mc(p,n)])
    
  assert fp.query(And(mc(m,n),n < 90)) == unsat
  assert fp.query(And(mc(m,n),n < 91)) == unsat
  assert fp.query(And(mc(m,n),n < 92)) == sat

def test_to_1():
  mc = Function('mc', IntSort(), IntSort(), BoolSort())
  n, m, p = Ints('m n p')

  fp = Fixedpoint()

  fp.declare_var(n,m,p)
  fp.register_relation(mc)

  fp.rule(mc(m, 1), m <= 1)
  fp.rule(mc(m, n), [m > 1 , mc(m-1, n)])
    
  assert fp.query(And(mc(m,n),n != 1)) == unsat

def test_aseq():
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  mc = Function('mc', IntSort(), IntSort(), BoolSort())
  n, m, p = Ints('m n p')

  fp = Fixedpoint()

  fp.declare_var(n,m,p)
  fp.register_relation(mc, add)

  fp.fact(add(m, n, m + n)) # if *, doesn't work!
  fp.rule(mc(m, 1), m <= 1)
  fp.rule(mc(m, n), [m > 1 , mc(m-1, p), add(m, p, n)])
    
  assert fp.query(And(mc(m,n),n < 1)) == unsat
  assert fp.query(And(mc(m,n),n < 2)) == sat
  assert fp.query(And(mc(m,n),n > 100 )) == sat
  assert fp.query(mc(5,15)) == sat
  assert fp.query(mc(5,16)) == unsat

@pytest.mark.skip
def test_mseq_hangs():
  mul = Function('mul', IntSort(), IntSort(), IntSort(), BoolSort())
  mc = Function('mc', IntSort(), IntSort(), BoolSort())
  n, m, p = Ints('m n p')

  fp = Fixedpoint()

  fp.declare_var(n,m,p)
  fp.register_relation(mc, mul)

  fp.fact(mul(m, n, m * n))
  fp.rule(mc(m, 1), m <= 1)
  fp.rule(mc(m, n), [m > 1 , mc(m-1, p), mul(m, p, n)])
    
  assert fp.query(And(mc(m,n),n < 1)) == unsat
  assert fp.query(And(mc(m,n),n < 2)) == sat
  assert fp.query(And(mc(m,n),n > 100 )) == sat
  assert fp.query(mc(5,120)) == sat
  assert fp.query(mc(5,24)) == unsat

def test_mseq():
  mul = Function('mul', IntSort(), IntSort(), IntSort(), BoolSort())
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  neg = Function('neg', IntSort(), IntSort(), BoolSort())
  mc = Function('mc', IntSort(), IntSort(), BoolSort())
  n, m, p, o = Ints('m n p o')

  fp = Fixedpoint()

  fp.declare_var(n,m,p,o)
  fp.register_relation(mc, add, mul, neg)

  fp.fact(add(m, n, m + n))
  fp.fact(neg(m, -m))
  fp.rule(mul(m, n, 0), n == 0)
  fp.rule(mul(m, n, m), n == 1)
  fp.rule(mul(m, n, o), [n < 0, mul(m,n,p), neg(p,o)])
  fp.rule(mul(m, n, o), [n > 1, mul(m,n-1,p), add(m,p,o)])
  fp.rule(mc(m, 1), m <= 1)
  fp.rule(mc(m, n), [m > 1 , mc(m-1, p), mul(m, p, n)])
    
  assert fp.query(And(mc(m,n),n < 1)) == unsat
  assert fp.query(And(mc(m,n),n < 2)) == sat
  assert fp.query(And(mc(m,n),n > 100 )) == sat
  assert fp.query(mc(5,120)) == sat
  assert fp.query(mc(5,24)) == unsat

def test_fib():
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  mc = Function('mc', IntSort(), IntSort(), BoolSort())
  n, m, p, o = Ints('m n p o')

  fp = Fixedpoint()

  fp.declare_var(n,m,p,o)
  fp.register_relation(mc, add)

  fp.fact(add(m, n, m + n))
  fp.rule(mc(m, 1), m <= 1)
  fp.rule(mc(m, o), [m > 1 , mc(m-1, p), mc(m-2, n), add(p, n, o)])
    
  assert fp.query(And(mc(m,n),n < 1)) == unsat
  assert fp.query(And(mc(m,n),n < 2)) == sat
  assert fp.query(And(mc(m,n),n > 100 )) == sat
  assert fp.query(And(mc(m,n),n == 21, m == 7 )) == sat
  assert fp.query(And(mc(m,n),n == 21, m == 6 )) == unsat