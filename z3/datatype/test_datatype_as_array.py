from z3 import *

def test_datatype_as_function():
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

def test_exclusive_datatype_as_function():
    # we will set up foo where x is x + 1 if it is an int and x + 2 if it is a real
    # we will set up bar where x is x + 1 if it is an int
    # intuitively, the domain of foo includes the domain of bar, and we want it to validate as such
    # in other words, we want to prove that there is NOT an elt in bar but not in foo
    # whereas we want to prove that there IS an elt in foo but not in bar
    ForAll