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

def test_equivalent_functions():
  to_15 = Function('to_15', IntSort(), IntSort(), BoolSort())
  is_15 = Function('is_15', IntSort(), IntSort(), BoolSort())
  n, m, p = Ints('n m p')

  fp = Fixedpoint()

  fp.declare_var(n,m,p)
  fp.register_relation(to_15, is_15)

  fp.fact(is_15(m, 15))
  fp.fact(to_15(15, 15))
  fp.rule(to_15(m, n), [m < 15, to_15(m + 1, n)])
  fp.rule(to_15(m, n), [m > 15, to_15(m - 1, n)])

  assert fp.query(Exists([m, n, p], And(to_15(m,n), is_15(m,p), n != p))) == unsat


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

def test_encoding_partial_application():
  P = Datatype('P')
  P.declare('P')
  P = P.create()
  partial_add = Function('partial_add', IntSort(), P, BoolSort())
  resolved_add = Function('resolved_add', P, IntSort(), IntSort(), BoolSort())
  fp = Fixedpoint()
  p, q = Consts('p q', P)
  x,y,z = Ints('x y z')
  fp.declare_var(p, q, x, y, z)
  fp.register_relation(partial_add, resolved_add)
  fp.rule(resolved_add(p, y, z), [partial_add(x, p), z == x + y])
  # curry 5
  fp.fact(partial_add(5, p))
  fp.fact(partial_add(12, q))
  assert fp.query(resolved_add(p, 11, 16)) == sat
  assert fp.query(resolved_add(p, 11, 15)) == unsat
  assert fp.query(resolved_add(q, 11, 23)) == sat
  assert fp.query(resolved_add(q, 11, 12)) == unsat

# works well, but impossible to incode infinite sequences meaningfully
# sequences seem to need to be bound with a terminating condition to
# get anything useful, and furthermore, even if they weren't, it is
# not clear how it would be possible to construct an infinite sequence
# for uncountable things (ie reals)
def test_ll_sum_custom_function():
  list_sum = Function('list_sum', IntSort(), IntSort(), BoolSort())
  set_sum = Function('set_sum', IntSort(), IntSort(), BoolSort())
  list_len = Function('list_len', IntSort(), IntSort(), BoolSort())
  set_len = Function('set_len', IntSort(), IntSort(), BoolSort())
  cons = Function('cons', IntSort(), IntSort(), IntSort(), BoolSort())
  car = Function('car', IntSort(), IntSort(), BoolSort())
  has = Function('has', IntSort(), IntSort(), BoolSort())
  does_not_have = Function('does_not_have', IntSort(), IntSort(), BoolSort())
  add = Function('add', IntSort(), IntSort(), IntSort(), BoolSort())
  a,b,c,d,e,f,g,h,i = Ints('a b c d e f g h i')
  x,y,z = Bools('x y z')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d,e,f,g,h,i,x,y,z)
  fp.register_relation(list_sum, set_sum, list_len, set_len, cons, add, car, has, does_not_have)
  fp.fact(add(a, b, a + b))
  fp.rule(list_sum(a, 0), a <= 0)
  fp.rule(set_sum(a, 0), a <= 0)
  fp.rule(list_len(a, 0), a <= 0)
  fp.rule(set_len(a, 0), a <= 0)
  fp.rule(car(a, b), [a > 0, cons(b, a - 1, a)])
  fp.rule(list_sum(a, i), [a > 0, cons(b, a - 1, a), list_sum(a - 1, c), add(b, c, i)])
  fp.rule(set_sum(a, i), [a > 0, cons(b, a - 1, a), does_not_have(a-1, b), set_sum(a - 1, c), add(b, c, i)])
  fp.rule(set_sum(a, i), [a > 0, cons(b, a - 1, a), has(a-1, b), set_sum(a - 1, i)])
  fp.rule(list_len(a, i), [a > 0, cons(b, a - 1, a), list_len(a - 1, c), add(1, c, i)])
  fp.rule(set_len(a, i), [a > 0, cons(b, a - 1, a), does_not_have(a-1, b), set_len(a - 1, c), add(1, c, i)])
  fp.rule(set_len(a, i), [a > 0, cons(b, a - 1, a), has(a-1, b), set_len(a - 1, i)])
  fp.rule(has(a, b), [a > 0, cons(c, a - 1, a), Or(c == b, has(a - 1, b))])
  fp.fact(does_not_have(0, b))
  fp.rule(does_not_have(a, b), [a > 0, cons(c, a - 1, a), And(c != b, does_not_have(a - 1, b))])
  # build our list
  #L = 4 # anything above 10 and it really slows stuff down...
  #for x in range(L):
  #  fp.fact(cons(5 if x % 2 == 0 else 6, x, x+1))
  # make assertions
  # assert fp.query(list_sum(0, 0)) == sat
  # assert fp.query(list_sum(2,12)) == unsat
  # assert fp.query(list_sum(2,11)) == sat
  # assert fp.query(list_sum(4,22)) == sat
  # assert fp.query(list_sum(4,16)) == unsat
  # assert fp.query(set_sum(4,11)) == sat
  # assert fp.query(set_sum(4,12)) == unsat
  # assert fp.query(set_sum(4,16)) == unsat
  # assert fp.query(set_sum(L,11)) == sat
  # assert fp.query(list_len(0, 0)) == sat
  # assert fp.query(list_len(2,12)) == unsat
  # assert fp.query(list_len(2,2)) == sat
  # assert fp.query(list_len(4,4)) == sat
  # assert fp.query(list_len(L,L)) == sat
  # assert fp.query(set_len(4,2)) == sat 
  # assert fp.query(set_len(4,1)) == unsat
  # assert fp.query(set_len(4,3)) == unsat
  # assert fp.query(set_len(L,2)) == sat
  # assert fp.query(car(1, 5)) == sat
  # assert fp.query(car(1, 6)) == unsat
  # assert fp.query(has(2, 5)) == sat
  # assert fp.query(has(2, 6)) == sat
  # assert fp.query(has(4, 6)) == sat
  # assert fp.query(does_not_have(4, 6)) == unsat
  # assert fp.query(has(2, 5)) == sat
  # assert fp.query(has(2, 4)) == unsat
  # assert fp.query(does_not_have(2, 4)) == sat
  # assert fp.query(has(0, 4)) == unsat
  # assert fp.query(has(0, 5)) == unsat
  # assert fp.query(has(1, 5)) == sat
  # fp.rule(cons(a, b, c), a < 0)
  fp.rule(cons(a, b, b + 1), a < 0)
  #fp.fact(cons(-1, 1, 2))
  assert fp.query(And(list_sum(a, b), a > 0, b < 0)) == sat
  assert fp.query(And(list_sum(a, b), a > 0, b == 0)) == unsat

def test_avg():
  list_sum = Function('list_sum', IntSort(), IntSort(), BoolSort())
  cons = Function('cons', IntSort(), IntSort(), IntSort(), BoolSort())
  a,b,c,d,e = Ints('a b c d e')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d,e)
  fp.register_relation(list_sum, cons)
  fp.rule(list_sum(a, 0), a == 0)
  fp.rule(list_sum(a, d), [a > 0, cons(b, a - 1, a), list_sum(a - 1, c), b + c == d])
  fp.fact(cons(a, b, b + 1))
  '''
  assert fp.query(And(list_sum(a, b),
    list_sum(c, d),
    c > 0,
    a == c + 1, # a is 1 longer than c
    cons(e, c, a),
    (((e * d) - (c * d) )**2) < (((e * b) - (a * b))**2)
    )) == unsat
  assert fp.query(And(list_sum(a, b),
    list_sum(c, d),
    c > 0,
    a == c + 1, # a is 1 longer than c
    cons(e, c, a),
    (((e * d) - (c * d) )**2) >= (((e * b) - (a * b))**2)
    )) == sat
  '''

def test_negative_list_sum_ll():
  ll = Datatype('ll')
  ll.declare('empty')
  ll.declare('cons', ('car', IntSort()), ('cdr', ll))
  ll = ll.create()
  list_sum = Function('list_sum', ll, IntSort(), BoolSort())
  a,e = Consts('a e', ll)
  b,c,d = Ints('b c d')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d,e)
  fp.register_relation(list_sum)
  fp.rule(list_sum(a, 0), a == ll.empty)
  fp.rule(list_sum(a, d), [a != ll.empty, b < 0, ll.cons(b, e) == a, list_sum(e, c), b + c == d])
  assert fp.query(And(list_sum(a, b), a != ll.empty, b < 0)) == sat
  assert fp.query(And(list_sum(a, b), a != ll.empty, b >= 0)) == unsat

def test_negative_list_sum():
  list_sum = Function('list_sum', IntSort(), IntSort(), BoolSort())
  cons = Function('cons', IntSort(), IntSort(), IntSort(), BoolSort())
  a,b,c,d = Ints('a b c d')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d)
  fp.register_relation(list_sum, cons)
  fp.rule(list_sum(a, 0), a == 0)
  fp.rule(list_sum(a, d), [a > 0, cons(b, a - 1, a), list_sum(a - 1, c), b + c == d])
  fp.rule(cons(a, b, b + 1), a < 0)
  assert fp.query(And(list_sum(a, b), a > 0, b < 0)) == sat
  assert fp.query(And(list_sum(a, b), a > 0, b >= 0)) == unsat

def test_list_elt_gt_1():
  ll = Datatype('ll')
  ll.declare('empty')
  ll.declare('cons', ('car', IntSort()), ('cdr', ll))
  ll = ll.create()
  list_sum = Function('list_sum', ll, IntSort(), BoolSort())
  list_len = Function('list_len', ll, IntSort(), BoolSort())
  a,e = Consts('a e', ll)
  b,c,d = Ints('b c d')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d,e)
  fp.register_relation(list_sum, list_len)
  fp.rule(list_sum(a, 0), a == ll.empty)
  fp.rule(list_sum(a, d), [a != ll.empty, b < 1, ll.cons(b, e) == a, list_sum(e, c), b + c == d])
  fp.rule(list_len(a, 0), a == ll.empty)
  fp.rule(list_len(a, d), [a != ll.empty, b < 1, ll.cons(b, e) == a, list_len(e, c), 1 + c == d])
  assert fp.query(And(list_sum(a, b), list_len(a, c), a != ll.empty, b >= c)) == unsat
  assert fp.query(And(list_sum(a, b), list_len(a, c), a != ll.empty, b < c)) == sat

# freezes
@pytest.mark.skip
def test_list_rev():
  ll = Datatype('ll')
  ll.declare('empty')
  ll.declare('cons', ('car', IntSort()), ('cdr', ll))
  ll = ll.create()
  list_sum = Function('list_sum', ll, IntSort(), BoolSort())
  list_tran = Function('list_tran', ll, ll, ll, BoolSort())
  list_rev = Function('list_rev', ll, ll, BoolSort())
  a,e,f,g,h = Consts('a e f g h', ll)
  b,c,d = Ints('b c d')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d,e,f,g,h)
  fp.register_relation(list_sum, list_rev, list_tran)
  fp.rule(list_sum(a, 0), a == ll.empty)
  fp.rule(list_sum(a, d), [a != ll.empty, b < 1, ll.cons(b, e) == a, list_sum(e, c), b + c == d])
  fp.fact(list_tran(ll.empty, e, e))
  fp.rule(list_tran(a,e,h), [ll.cons(b, f) == a, ll.cons(b, e) == g, list_tran(f, g, h)])
  fp.rule(list_rev(a,e), list_tran(a, ll.empty, e))
  assert fp.query(list_rev(a,e), list_rev(e, f), a != f) == unsat

# also freezes
@pytest.mark.skip
def test_list_rev():
  ll = Datatype('ll')
  ll.declare('empty')
  ll.declare('cons', ('car', IntSort()), ('cdr', ll))
  ll = ll.create()
  list_app = Function('list_app', ll, ll, ll, BoolSort())
  list_rev = Function('list_rev', ll, ll, BoolSort())
  a,e,f,g,h = Consts('a e f g h', ll)
  b,c,d = Ints('b c d')
  
  fp = Fixedpoint()
  fp.declare_var(a,b,c,d,e,f,g,h)
  fp.register_relation(list_rev, list_app)
  fp.fact(list_app(ll.empty, e, e))
  fp.fact(list_app(e, ll.empty, e))
  fp.rule(list_app(a,e,h), [ll.cons(b, f) == a, list_app(f, e, g), ll.cons(b, g) == h])
  fp.fact(list_rev(ll.empty,ll.empty))
  fp.rule(list_rev(a,e), [ll.cons(b, f) == a, ll.cons(b, ll.empty) == g, list_rev(f, h), list_app(h, g, e)])
  assert fp.query(list_rev(a,e), list_rev(e, f), a != f) == unsat

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