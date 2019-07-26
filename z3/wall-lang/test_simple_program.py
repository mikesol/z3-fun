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


def test_simple_program_using_set_to_represent_addition():
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
    i_i_pair, mk_i_i_pair, (i_i_first, i_i_second) = TupleSort("i_i_pair", [IntSort(), IntSort()])
    i_si_pair, mk_i_si_pair, (i_si_first, i_si_second) = TupleSort("i_si_pair", [IntSort(), SetSort(i_i_pair)])
    free_i_si_pair = Const('free_i_si_pair', i_si_pair)
    free_i_i = Const('free_i_i', i_i_pair)
    addition = Const('addition', SetSort(i_si_pair))
    s.add(addition == Lambda([free_i_si_pair],
        i_si_second(free_i_si_pair) == Lambda([free_i_i],
            i_si_first(free_i_si_pair) + i_i_first(free_i_i) == i_i_second(free_i_i))))
    res = Const('res', i_si_pair)
    subres = Const('subres', i_i_pair)
    s.add(addition[res])
    s.add(i_si_first(res) == a)
    s.add(i_i_first(subres) == b)
    s.add(i_si_second(res)[subres])
    s.add(c == i_i_second(subres))
    assert s.check() == sat
    # above here, we have proven that the program is possible
    # below, we prove that the result is 3 and not 4
    s.push()
    s.add(i_i_second(subres) == 3)
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(i_i_second(subres) == 4)
    assert s.check() == unsat

def test_simple_program_with_conditional():
    '''
    a = rand 0
    b = ? < a 0.5 0 1
    c = + 3 b
    c
    // should compile
    '''
    s = Solver()
    # line 1
    a = Real('a')
    s.add(a >= 0)
    s.add(a < 1)
    assert s.check() == sat
    # line 2
    r_r_pair, mk_r_r_pair, (r_r_first, r_r_second) = TupleSort("r_r_pair", [RealSort(), BoolSort()])
    r_sr_pair, mk_r_sr_pair, (r_sr_first, r_sr_second) = TupleSort("r_sr_pair", [RealSort(), SetSort(r_r_pair)])
    free_r_sr_pair = Const('free_r_sr_pair', r_sr_pair)
    free_r_r = Const('free_r_r', r_r_pair)
    lessthan = Const('lessthan', SetSort(r_sr_pair))
    s.add(lessthan == Lambda([free_r_sr_pair],
        r_sr_second(free_r_sr_pair) == Lambda([free_r_r],
            (r_sr_first(free_r_sr_pair) < r_r_first(free_r_r)) == r_r_second(free_r_r))))
    _b_res = Const('_b_res', r_sr_pair)
    _b_subres = Const('_b_subres', r_r_pair)
    s.add(lessthan[_b_res])
    s.add(r_sr_first(_b_res) == a)
    s.add(r_r_first(_b_subres) == 0.5)
    s.add(r_sr_second(_b_res)[_b_subres])
    _tf_result = r_r_second(_b_subres)
    b = Int('b')
    b_i_pair, mk_b_i_pair, (b_i_first, b_i_second) = TupleSort("b_i_pair", [BoolSort(), IntSort()])
    if_now = EmptySet(b_i_pair)
    if_now = Store(if_now, mk_b_i_pair(_tf_result, 0), True)
    if_now = Store(if_now, mk_b_i_pair(Not(_tf_result), 1), True)
    free_b_i_pair = Const('free_b_i_pair', b_i_pair)
    s.add(if_now[free_b_i_pair])
    s.add(b == b_i_second(free_b_i_pair))
    assert s.check() == sat
    # line 3
    c = Int('c')
    i_i_pair, mk_i_i_pair, (i_i_first, i_i_second) = TupleSort("i_i_pair", [IntSort(), IntSort()])
    i_si_pair, mk_i_si_pair, (i_si_first, i_si_second) = TupleSort("i_si_pair", [IntSort(), SetSort(i_i_pair)])
    free_i_si_pair = Const('free_i_si_pair', i_si_pair)
    free_i_i = Const('free_i_i', i_i_pair)
    addition = Const('addition', SetSort(i_si_pair))
    s.add(addition == Lambda([free_i_si_pair],
        i_si_second(free_i_si_pair) == Lambda([free_i_i],
            i_si_first(free_i_si_pair) + i_i_first(free_i_i) == i_i_second(free_i_i))))
    res = Const('res', i_si_pair)
    subres = Const('subres', i_i_pair)
    s.add(addition[res])
    s.add(i_si_first(res) == 3)
    s.add(i_i_first(subres) == b)
    s.add(i_si_second(res)[subres])
    s.add(c == i_i_second(subres))
    assert s.check() == sat
    # above here, we have proven that the program is possible
    # below, we prove that the result could be 3 or 4, but not 5
    s.push()
    s.add(i_i_second(subres) == 3) # 3 + 0
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(i_i_second(subres) == 4) # 3 + 1
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(i_i_second(subres) == 5)
    assert s.check() == unsat

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
    # One strategy is to construct the everything datatype dynamically
    # from the currently available values and then determine if the incoming set has
    # the same accessors
    c__ = ArraySort(IntSort(), IntSort())
    c_ = Array('c_', IntSort(), c__)
    c_free_0, c_free_1 = Ints('c_free_0 c_free_1')
    s.add(c_ == Lambda([c_free_0], Lambda([c_free_1], c_free_0 + c_free_1)))
    UnknownSort = DeclareSort('UnknownSort')
    Unknown = Const('Unknown', UnknownSort)
    Everything = Datatype('Everything')
    Everything.declare('int', ('i', IntSort()))
    Everything.declare('unknown', ('u', UnknownSort)) # everthings always have an unknown to distinguish as everything
    Everything = Everything.create()
    # kind of hackish here - basically, we'd need something to iterate
    # over function declarations attached to the datatype and line them up
    # the everything constructor would always have to delay evaluation
    # so that it created the world anew every time
    # for example, if we have `a = map everything id` and later we
    # want to use `a`, it needs to recreate the world again
    # in general, one strategy could be that for everything we encounter,
    # we create the world and set the appropriate things to never
    # for example, 1 would be World.int(1)
    # In this way, `+ 3 'foo` would construct a plus with a World of string and int,
    # set everything not int to never, and then fail because it gets World.string('foo')
    assert Everything.i.range() == c_.sort().domain()
    assert Everything.u.range() != c_.sort().domain() # so this is where it breaks