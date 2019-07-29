from z3 import *
import pytest
from functools import reduce

@pytest.mark.skip # because too slow...
def test_cannot_handle_recursively_defined_array():
    a = Array('a', IntSort(), IntSort())
    s = Solver()
    x, y, c, d = Ints('x y c d')
    s.add(a[15] == 15)
    s.add(ForAll([x], Implies(x > 15, a[x] == a[x-1])))
    s.add(ForAll([y], Implies(y < 15, a[y] == a[y+1])))
    s.add(a[c] != 15)
    assert s.check() == unknown

# bombs
@pytest.mark.skip
def test_cannot_handle_recursively_defined_array():
    a = Array('a', IntSort(), IntSort())
    b = Array('b', IntSort(), IntSort())
    s = Solver()
    c, d = Ints('c d')
    s.add(a == Lambda([d], If(d==15, d, If(d>15, a[d-1], a[d+1]))))
    s.add(b == Lambda(c, IntVal(15)))
    s.add(a != b)
    assert s.check() == unsat

# should be unsat, but generates sat
# it things a = K(i, False) and generates a model where
# y can be (63, 15), which clearly should lead to unsat when wrapped in Not,
# as it DOES satisfy the array as defined below
# why?
@pytest.mark.skip
def test_cannot_handle_recursively_defined_set_of_pairs():
    pair, mk_pair, (first, second) = TupleSort('i', [IntSort(), IntSort()])
    a = Const('a',SetSort(pair))
    s = Solver()
    x = Const('x', pair)
    s.add(a == Lambda([x],
        If(And(first(x) == 15, second(x) == 15), True,
            If(And(first(x) == 15, second(x) != 15), False,
            If(first(x) < 15, a[mk_pair(first(x) + 1, second(x))],
            a[mk_pair(first(x) - 1, second(x))])))))
    y = Const('y', pair)
    s.push()
    s.add(second(y) == 15)
    s.add(Not(a[y]))
    assert s.check() == unsat

def test_faux_recursive_function():
    to15 = RecFunction('to15', IntSort(), IntSort())
    i, x, y = Ints('i x y')
    arr0 = Array('arr0', IntSort(), IntSort())
    TARGET = 12 # anything larger hangs a long time
    to15 = lambda m, n: 15 if n == TARGET else If(m == 15, m, to15(m + If(m > 15, -1, 1), n + 1))
    lamb = Lambda([i], to15(i, 0))
    s = Solver()
    s.add(arr0 == lamb)
    s.add(arr0[x] != 15)
    assert s.check() == unsat

def test_flattened_recursive_structure():
    '''
    It is possible to create a fibonaci series with an array
    '''
    MaybeInt = Datatype('MaybeInt')
    MaybeInt.declare('int', ('i', IntSort()))
    MaybeInt.declare('never')
    MaybeInt = MaybeInt.create()
    x = Const('x', MaybeInt)
    arr0 = Array('arr0', MaybeInt, MaybeInt)
    arr1 = Array('arr1', MaybeInt, MaybeInt)
    s = Solver()
    s.add(arr0 == Lambda([x],
        If(
            Or(x == MaybeInt.never, And(MaybeInt.is_int(x), MaybeInt.i(x) < 0)),
            MaybeInt.never,
            If(
                MaybeInt.i(x) == 0,
                MaybeInt.int(1),
                MaybeInt.int(MaybeInt.i(x) * MaybeInt.i(arr0[MaybeInt.int(MaybeInt.i(x) - 1)]))))))
    s.push()
    s.add(arr0[MaybeInt.int(5)] == MaybeInt.int(5 * 4  * 3 * 2 * 1))
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(arr0[MaybeInt.int(6)] == MaybeInt.int(5 * 4  * 3 * 2 * 1))
    assert s.check() == unsat

def test_reduce():
    linkedlist = Datatype('linkedlist')
    linkedlist.declare('end')
    linkedlist.declare('cons', ('car', IntSort()), ('cdr', linkedlist))
    linkedlist = linkedlist.create()
    cons = linkedlist.cons
    car = linkedlist.car
    cdr = linkedlist.cdr
    end = linkedlist.end
    is_end = linkedlist.is_end
    a = Array('a', linkedlist, IntSort())
    b = cons(1, cons(2, cons(3, cons(4, cons(5, end)))))
    s = Solver()
    x = Const('x', linkedlist)
    s.add(a == Lambda([x], If(is_end(x), 0, car(x) + a[cdr(x)])))
    s.push()
    s.add(a[b] == 15)
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(a[b] == 16)
    assert s.check() == unsat

def test_accessor():
    maybe = Datatype('maybe')
    maybe.declare('int', ('i', IntSort()))
    maybe.declare('never')
    maybe = maybe.create()
    linkedlist = Datatype('linkedlist')
    linkedlist.declare('end')
    linkedlist.declare('cons', ('car', IntSort()), ('cdr', linkedlist))
    linkedlist = linkedlist.create()
    cons = linkedlist.cons
    car = linkedlist.car
    cdr = linkedlist.cdr
    end = linkedlist.end
    is_end = linkedlist.is_end
    a = Array('a', IntSort(), ArraySort(linkedlist, maybe))
    b = cons(1, cons(2, cons(3, cons(4, cons(5, end)))))
    s = Solver()
    x = Const('x', linkedlist)
    y = Const('y', IntSort())
    s.add(a == Lambda([y],
        Lambda([x],
            If(Or(is_end(x), y < 0),
                maybe.never,
                If(y == 0,
                maybe.int(car(x)),
                a[y-1][cdr(x)])))))
    s.push()
    s.add(a[0][b] == maybe.int(1))
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(a[0][b] == maybe.int(100))
    assert s.check() == unsat
    s.pop()
    s.push()
    s.add(a[100][b] == maybe.never)
    assert s.check() == sat