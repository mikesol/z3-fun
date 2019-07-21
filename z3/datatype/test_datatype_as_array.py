from z3 import *
import pytest

def test_datatype_as_array():
    # basically turns datatype into an array
    FakeArray = Datatype('FakeArray')
    FakeArray.declare('ii', ('i', IntSort()))
    FakeArray.declare('rr', ('r', RealSort()))
    FakeArray.declare('bb', ('b', BoolSort()))
    FakeArray.declare('ss', ('s', StringSort()))
    FakeArray.declare('pp', ('p', FakeArray))
    FakeArray.declare('pf', ('dom', FakeArray), ('ran', FakeArray))
    FakeArray = FakeArray.create()
    ii = FakeArray.ii
    i = FakeArray.i
    rr = FakeArray.rr
    r = FakeArray.r
    bb = FakeArray.bb
    b = FakeArray.b
    ss = FakeArray.ss
    s = FakeArray.s
    pf = FakeArray.pf
    dom = FakeArray.dom
    ran = FakeArray.ran
    foo = pf(ii(Int('x')), ii(Int('y')))
    solver = Solver()
    solver.add(i(dom(foo)) == (i(ran(foo)) - 1)) # x = y - 1
    solver.add(And(i(dom(foo)) == 3, i(ran(foo)) == 4)) # this fulfills it
    assert solver.check() == sat # so sat
    solver = Solver()
    solver.add(i(dom(foo)) == (i(ran(foo)) - 1)) # x = y - 1
    solver.add(And(i(dom(foo)) == 3, i(ran(foo)) == 3)) # this breaks it
    assert solver.check() == unsat # so unsat

def test_exclusive_datatype_as_array():
    # we will set up a1 where x is in domain if less than 5 and int or less than 6 and real
    # we will set up a0 where x is in domain if less than 5 and int
    # intuitively, the domain of a0 includes the domain of a1, and we want it to validate as such
    # in other words, we want to prove that there is NOT an elt in a1 but not in a0
    # whereas we want to prove that there IS an elt in a0 but not in a1    
    IntOrReal = Datatype("IntOrReal")
    IntOrReal.declare('int', ('i', IntSort()))
    IntOrReal.declare('real', ('r', RealSort()))
    IntOrReal = IntOrReal.create()
    a0 = Array('a0', IntOrReal, BoolSort())
    a1 = Array('a1', IntOrReal, BoolSort())
    x = Const('x', IntOrReal)
    b = Bool('b')
    bb = Bool('bb')
    s = Solver()
    s.add(b == False)
    s.add(bb == True)
    s.add(a0 == Lambda([x], If(
        And(IntOrReal.is_int(x), IntOrReal.i(x) < 5), bb, b)))
    s.add(a1 == Lambda([x], If(
        And(IntOrReal.is_int(x), IntOrReal.i(x) < 5), bb, If(
            And(IntOrReal.is_real(x), IntOrReal.r(x) < 6.0), bb, b
        ))))
    y = Const('y', IntOrReal)
    s.push()
    s.add(Exists([y], And(a1[y], Not(a0[y]))))
    assert s.check() == sat
    s.pop()
    s.add(Exists([y], And(a0[y], Not(a1[y]))))
    assert s.check() == unsat

def test_exclusive_datatype_as_array_2():
    # almost same as above
    # we will set up a1 where x is in domain if less than 5 and int or less than 6 and real
    # we will set up a0 where x is in domain if less than 4 and int
    # intuitively, the domain of a0 includes the domain of a1, and we want it to validate as such
    # in other words, we want to prove that there is NOT an elt in a1 but not in a0
    # whereas we want to prove that there IS an elt in a0 but not in a1    
    IntOrReal = Datatype("IntOrReal")
    IntOrReal.declare('int', ('i', IntSort()))
    IntOrReal.declare('real', ('r', RealSort()))
    IntOrReal = IntOrReal.create()
    a0 = Array('a0', IntOrReal, BoolSort())
    a1 = Array('a1', IntOrReal, BoolSort())
    x = Const('x', IntOrReal)
    b = Bool('b')
    bb = Bool('bb')
    s = Solver()
    s.add(b == False)
    s.add(bb == True)
    s.add(a0 == Lambda([x], If(
        And(IntOrReal.is_int(x), IntOrReal.i(x) < 4), bb, b)))
    s.add(a1 == Lambda([x], If(
        And(IntOrReal.is_int(x), IntOrReal.i(x) < 5), bb, If(
            And(IntOrReal.is_real(x), IntOrReal.r(x) < 6.0), bb, b
        ))))
    y = Const('y', IntOrReal)
    s.push()
    s.add(Exists([y], And(a1[y], Not(a0[y]))))
    assert s.check() == sat
    s.pop()
    s.add(Exists([y], And(a0[y], Not(a1[y]))))
    assert s.check() == unsat

def test_exclusive_datatype_as_array_3():
    # almost same as above
    # we will set up a1 where x is in domain if less than 5 and int or less than 6 and real
    # we will set up a0 where x is in domain if less than 6 and int
    # neither of the domains overlap, so both conditions should be sat
    IntOrReal = Datatype("IntOrReal")
    IntOrReal.declare('int', ('i', IntSort()))
    IntOrReal.declare('real', ('r', RealSort()))
    IntOrReal = IntOrReal.create()
    a0 = Array('a0', IntOrReal, BoolSort())
    a1 = Array('a1', IntOrReal, BoolSort())
    x = Const('x', IntOrReal)
    b = Bool('b')
    bb = Bool('bb')
    s = Solver()
    s.add(b == False)
    s.add(bb == True)
    s.add(a0 == Lambda([x], If(
        And(IntOrReal.is_int(x), IntOrReal.i(x) < 6), bb, b)))
    s.add(a1 == Lambda([x], If(
        And(IntOrReal.is_int(x), IntOrReal.i(x) < 5), bb, If(
            And(IntOrReal.is_real(x), IntOrReal.r(x) < 6.0), bb, b
        ))))
    y = Const('y', IntOrReal)
    s.push()
    s.add(Exists([y], And(a1[y], Not(a0[y]))))
    assert s.check() == sat
    s.pop()
    s.add(Exists([y], And(a0[y], Not(a1[y]))))
    assert s.check() == sat

def test_maybe_strategy_for_binary_int_op():
    '''
    To express contraints, we can use the Maybe monad to fail
    on missing constraint.
    '''
    MaybeInt = Datatype('MaybeInt')
    MaybeInt.declare('int', ('i', IntSort()))
    MaybeInt.declare('never')
    MaybeInt = MaybeInt.create()
    mi_mi = ArraySort(MaybeInt, MaybeInt)
    arr = Array('arr', MaybeInt, mi_mi)
    s = Solver()
    x, y = Consts('x y', MaybeInt)
    s.add(arr == Lambda([x],
        If(And(MaybeInt.is_int(x), MaybeInt.i(x) < 3),
        Lambda([y], If(And(MaybeInt.is_int(y), MaybeInt.i(y) < 5), MaybeInt.int(MaybeInt.i(x) + MaybeInt.i(y)), MaybeInt.never)),
        K(MaybeInt, MaybeInt.never))))
    s.add(arr[MaybeInt.int(1)][MaybeInt.int(2)] == MaybeInt.int(3)) # Addition works
    s.add(arr[MaybeInt.int(1)][MaybeInt.int(2)] != MaybeInt.int(5)) # Not addition won't work
    s.add(arr[MaybeInt.int(3)][MaybeInt.int(2)] == MaybeInt.never) # Out of domain0 won't work
    s.add(arr[MaybeInt.int(1)][MaybeInt.int(5)] == MaybeInt.never) # Out of domain1 won't work
    assert s.check() == sat

def test_domain_of_array_contained_within_another():
    '''
    We verify that one domain contains the other but not vice versa
    '''
    MaybeInt = Datatype('MaybeInt')
    MaybeInt.declare('int', ('i', IntSort()))
    MaybeInt.declare('never')
    MaybeInt = MaybeInt.create()
    mi_mi = ArraySort(MaybeInt, MaybeInt)
    arr0 = Array('arr0', MaybeInt, mi_mi)
    arr1 = Array('arr1', MaybeInt, mi_mi)
    s = Solver()
    x, y = Consts('x y', MaybeInt)
    s.add(arr0 == Lambda([x],
        If(And(MaybeInt.is_int(x), MaybeInt.i(x) < 3),
        Lambda([y], If(And(MaybeInt.is_int(y), MaybeInt.i(y) < 5), MaybeInt.int(MaybeInt.i(x) + MaybeInt.i(y)), MaybeInt.never)),
        K(MaybeInt, MaybeInt.never))))
    s.add(arr1 == Lambda([x],
        If(And(MaybeInt.is_int(x), MaybeInt.i(x) < 3),
        Lambda([y], If(And(MaybeInt.is_int(y), MaybeInt.i(y) < 8), MaybeInt.int(MaybeInt.i(x) + MaybeInt.i(y)), MaybeInt.never)),
        K(MaybeInt, MaybeInt.never))))
    # there exists an a and b that, when added together, get a nil in arr0 but not arr1
    a, b = Consts('a b', MaybeInt)
    s.push()
    s.add(
        MaybeInt.is_int(a),
        MaybeInt.is_int(b),
        arr0[a][b] == MaybeInt.never,
        arr1[a][b] != MaybeInt.never)
    assert s.check() == sat
    s.pop()
    s.add(
        MaybeInt.is_int(a),
        MaybeInt.is_int(b),
        arr0[a][b] != MaybeInt.never,
        arr1[a][b] == MaybeInt.never)
    assert s.check() == unsat