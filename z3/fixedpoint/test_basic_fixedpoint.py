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

#z3.z3types.Z3Exception: b'recursive predicate (= (:var 3) (cdr (:var 0))) occurs nested in the body of a rule'
@pytest.mark.skip
def test_ll_len_with_cdr():
  ll = Datatype('ll')
  ll.declare('end')
  ll.declare('cons', ('car', IntSort()), ('cdr', ll))
  ll = ll.create()
  length = Function('length', ll, IntSort(), BoolSort())
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  x,y,z = Ints('x y z')
  c, d, e = Consts('c d e', ll)
  lc = Const('lc', ArraySort(ll,ll))

  fp = Fixedpoint()
  fp.declare_var(x,y,z,c,d)
  fp.register_relation(length, add, ll.cdr)
  fp.fact(add(x,y,x+y))
  fp.rule(length(c, 0), ll.is_end(c))
  fp.rule(length(c, x), [ll.is_cons(c), add(1, z, x), length(ll.cdr(c), z)])
  assert fp.query(length(ll.end, 0)) == sat
  assert fp.query(length(ll.cons(0, ll.end), 1)) == sat

def test_ll_sum_custom_function():
  list_sum = Function('list_sum', IntSort(), IntSort(), BoolSort())
  set_sum = Function('set_sum', IntSort(), IntSort(), BoolSort())
  cons = Function('cons', IntSort(), IntSort(), IntSort(), BoolSort())
  car = Function('car', IntSort(), IntSort(), BoolSort())
  has = Function('has', IntSort(), IntSort(), BoolSort(), BoolSort())
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  eqq = Function('eqq', IntSort(), IntSort(), BoolSort(), BoolSort())
  orr = Function('orr', BoolSort(), BoolSort(), BoolSort(), BoolSort())
  a,b,c,d,e,f,g,h,i = Ints('a b c d e f g h i')
  x,y,z = Bools('x y z')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d,e,f,g,h,i,x,y,z)
  fp.register_relation(list_sum, set_sum, cons, add, car, has, eqq, orr)
  fp.fact(add(a, b, a + b))
  fp.rule(eqq(a,b,a==b))
  fp.rule(orr(x,y,Or(x,y)))
  fp.rule(list_sum(a, 0), a <= 0)
  fp.rule(set_sum(a, 0), a <= 0)
  fp.rule(car(a, b), [a > 0, cons(b, a - 1, a)])
  fp.rule(list_sum(a, i), [a > 0, cons(b, a - 1, a), list_sum(a - 1, c), add(b, c, i)])
  fp.rule(set_sum(a, i), [a > 0, has(a-1, i, False), cons(b, a - 1, a), set_sum(a - 1, c), add(b, c, i)])
  fp.rule(set_sum(a, i), [a > 0, has(a-1, i, True), set_sum(a - 1, i)])
  fp.rule(has(0, b, False))
  fp.rule(has(a, b, x), [a > 0, cons(c, a - 1, a), has(a - 1, b, y), eqq(c, b, z), orr(y, z, x)])
  assert fp.query(list_sum(0, 0)) == sat
  fp.fact(cons(5, 0, 1))
  fp.fact(cons(6, 1, 2))
  fp.fact(cons(5, 2, 3))
  fp.fact(cons(6, 3, 4))
  assert fp.query(list_sum(2,12)) == unsat
  assert fp.query(list_sum(2,11)) == sat
  assert fp.query(list_sum(4,22)) == sat
  assert fp.query(list_sum(4,16)) == unsat
  #assert fp.query(set_sum(4,16)) == unsat
  #assert fp.query(set_sum(4,11)) == sat 
  assert fp.query(car(1, 5)) == sat
  assert fp.query(car(1, 6)) == unsat
  assert fp.query(has(2, 5, True)) == sat
  assert fp.query(has(2, 6, True)) == sat
  assert fp.query(has(2, 6, False)) == unsat
  assert fp.query(has(4, 6, False)) == unsat
  assert fp.query(has(4, 6, True)) == sat
  assert fp.query(has(2, 5, True)) == sat
  assert fp.query(has(2, 4, True)) == unsat
  assert fp.query(has(0, 4, True)) == unsat
  assert fp.query(has(0, 5, True)) == unsat
  assert fp.query(has(1, 5, True)) == sat

@pytest.mark.skip
def test_aoc():
  one_less = Function('one_less', SetSort(IntSort()), SetSort(IntSort()), BoolSort())
  length = Function('one_less', SetSort(IntSort()), IntSort(), BoolSort())
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  es = EmptySet(IntSort())
  fs = FullSet(IntSort())
  x, y, z = Ints('x y z')
  a, b = Consts('a b', SetSort(IntSort()))
  fp = Fixedpoint()

  # len z = if z is empty 0 else 1 + len(ol(z))

  fp.declare_var(x,y,z,a,b)
  fp.register_relation(one_less, length, add)
  fp.fact(add(x,y,x+y))
  fp.rule(one_less(a, b), # one_less doesn't represent a function as anything can be chosen...
          [
            ForAll(x, Implies(Not(a[x]), Not(b[x]))),
            Implies(Exists(x, a[x]), Exists(x, And(a[x], Not(b[x])))),
            Implies(Exists(x, a[x]), Exists(x, ForAll(y, If(x==y, True, b[y]) == a[y])))])
  fp.rule(length(a, 0), ForAll(x, Not(a[x])))
  fp.rule(length(a, x), [Exists(y, a[y]), add(1, y, x), length(b, y), one_less(a, b)])

  assert fp.query(length(es, 0)) == sat
  assert fp.query(length(es, 1)) == unsat
  assert fp.query(length(Store(es, 0, True), 1)) == sat
  assert fp.query(length(Store(Store(es, 0, True), 1, True), 2)) == sat
  assert fp.query(length(Lambda(x, And(x >= 0, x < 2)), 2)) == sat # struggles with anything over 2
  #assert fp.query(length(Store(es, 0, True), 0)) == unsat # struggles with unsat


# does not work
# stuff like a[x] looks fishy...
# basically, anything that accesses an array with a quantifier or otherwise seems to break
# in this case, max_s is the culprit...
@pytest.mark.skip
def test_aoc_max():
  rme = Function('rme', SetSort(IntSort()), IntSort(), SetSort(IntSort()), BoolSort())
  max_s = Function('max_s', SetSort(IntSort()), IntSort(), BoolSort())
  length = Function('one_less', SetSort(IntSort()), IntSort(), BoolSort())
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  es = EmptySet(IntSort())
  fs = FullSet(IntSort())
  w, x, y, z = Ints('w x y z')
  a, b = Consts('a b', SetSort(IntSort()))
  fp = Fixedpoint()

  # len z = if z is empty 0 else 1 + len(ol(z))

  fp.declare_var(x,y,z,a,b)
  fp.register_relation(rme, max_s, length, add)
  fp.fact(add(x,y,x+y))
  fp.fact(rme(a, x, SetDel(a,x)))
  fp.rule(max_s(a, 0), ForAll(x, Not(a[x])))
  fp.rule(max_s(a, x), And(a[x], ForAll(y, Implies(a[y], y < x))))
  fp.rule(length(a, 0), ForAll(x, Not(a[x])))
  fp.rule(length(a, x), [Exists(w, a[w]), add(1, y, x), length(b, y), rme(a, z, b), max_s(a, z)])

  assert fp.query(length(es, 0)) == sat
  assert fp.query(length(es, 1)) == unsat
  assert fp.query(length(Store(es, 0, True), 1)) == sat
  assert fp.query(length(Store(Store(es, 0, True), 1, True), 2)) == sat
  assert fp.query(length(Lambda(x, And(x >= 0, x < 2)), 2)) == sat # struggles with anything over 2
  #assert fp.query(length(Store(es, 0, True), 0)) == unsat # struggles with unsat


@pytest.mark.skip
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