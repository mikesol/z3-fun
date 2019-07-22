from z3 import *

def test_simple_program():
    '''
    a = 1
    b = 2
    c = + b a
    c
    // should compile
    '''
    s = Solver()
    # line 1
    a = Int('a')
    s.add(a == 1)
    assert s.check() == sat
    # line 2
    b = Int('b')
    s.add(b == 2)
    assert s.check() == sat
    # line 3
    c = Int('c')
    c__ = ArraySort(IntSort(), IntSort())
    c_ = Array('c_', IntSort(), c__)
    c_free_0, c_free_1 = Ints('c_free_0 c_free_1')
    s.add(c_ == Lambda([c_free_0], Lambda([c_free_1], c_free_0 + c_free_1)))
    s.add(c == c_[a][b])
    assert s.check() == sat

def test_non_compiling_program_0():
    '''
    a = 1
    b = 2
    +no1 = f- + 1
    c = +no1 a b // fails here
    c
    // should not compile because 1 not in domain of +no1
    '''
    s = Solver()
    # line 1
    a = Int('a')
    s.add(a == 1)
    assert s.check() == sat
    # line 2
    b = Int('b')
    s.add(b == 2)
    assert s.check() == sat
    # line 3
    c__ = ArraySort(IntSort(), IntSort())
    c_ = Array('c_', IntSort(), c__)
    c_free_0, c_free_1 = Ints('c_free_0 c_free_1')
    s.add(c_ == Lambda([c_free_0], Lambda([c_free_1], c_free_0 + c_free_1)))
    f_not_allowed = Int('f_not_allowed')
    s.add(f_not_allowed == 1)
    MaybeInt = Datatype('MaybeInt')
    MaybeInt.declare('int', ('i', IntSort()))
    MaybeInt.declare('never')
    MaybeInt = MaybeInt.create()
    f__ = ArraySort(MaybeInt, MaybeInt)
    f_ = Array('f_', MaybeInt, f__)
    f_free_0, f_free_1 = Consts('f_free_0 f_free_1', MaybeInt)
    s.add(f_ == Lambda([f_free_0],
        If(
            And(MaybeInt.is_int(f_free_0), MaybeInt.i(f_free_0) == f_not_allowed),
            K(MaybeInt, MaybeInt.never),
            Lambda([f_free_1], If(
                Or(f_free_0 == MaybeInt.never, f_free_1 == MaybeInt.never),
                MaybeInt.never,
                MaybeInt.int(c_[MaybeInt.i(f_free_0)][MaybeInt.i(f_free_1)])
            )))))
    assert s.check() == sat
    # line 4
    c = Const('c', MaybeInt)
    s.add(c == f_[MaybeInt.int(a)][MaybeInt.int(b)])
    s.add(c != MaybeInt.never)
    assert s.check() == unsat # program should not compile

def test_non_compiling_program_1():
    '''
    a = 1
    b = 2
    +no1 = f- + 1
    +no1' = f- +no1 1 // fails here
    a
    // should not compile because 1 not in domain of +no1
    '''
    s = Solver()
    # line 1
    a = Int('a')
    s.add(a == 1)
    assert s.check() == sat
    # line 2
    b = Int('b')
    s.add(b == 2)
    assert s.check() == sat
    # line 3
    c__ = ArraySort(IntSort(), IntSort())
    c_ = Array('c_', IntSort(), c__)
    c_free_0, c_free_1 = Ints('c_free_0 c_free_1')
    s.add(c_ == Lambda([c_free_0], Lambda([c_free_1], c_free_0 + c_free_1)))
    f_not_allowed = Int('f_not_allowed')
    s.add(f_not_allowed == 1)
    MaybeInt = Datatype('MaybeInt')
    MaybeInt.declare('int', ('i', IntSort()))
    MaybeInt.declare('never')
    MaybeInt = MaybeInt.create()
    f__ = ArraySort(MaybeInt, MaybeInt)
    f_ = Array('f_', MaybeInt, f__)
    f_free_0, f_free_1 = Consts('f_free_0 f_free_1', MaybeInt)
    s.add(f_ == Lambda([f_free_0],
        If(
            And(MaybeInt.is_int(f_free_0), MaybeInt.i(f_free_0) == f_not_allowed),
            K(MaybeInt, MaybeInt.never),
            Lambda([f_free_1], If(
                Or(f_free_0 == MaybeInt.never, f_free_1 == MaybeInt.never),
                MaybeInt.never,
                MaybeInt.int(c_[MaybeInt.i(f_free_0)][MaybeInt.i(f_free_1)])
            )))))
    assert s.check() == sat
    # line 4
    not_in_domain = MaybeInt.int(1)
    s.add(f_[not_in_domain] != K(MaybeInt, MaybeInt.never))
    assert s.check() == unsat # program should not compile

def test_non_compiling_program_2():
    '''
    a = 1
    b = 2
    z = map everything + // fails here
    a
    // should not compile because parts of everything are not in the domain of +
    '''
    pass