from z3 import *

def test_datatype_as_enum():
    Foo = Datatype("Foo")
    Foo.declare('foo')
    Foo.declare('bar')
    Foo = Foo.create()
    a0 = Array('f', Foo, BoolSort())
    a1 = Array('m', Foo, BoolSort())
    x = Const('x', Foo)
    s = Solver()
    s.add(ForAll([x], a0[x] == If(x == Foo.foo, True, False)))
    s.add(ForAll([x], a1[x] == True))
    s.add(IsSubset(a0, a1))
    assert s.check() == sat
    s = Solver()
    s.add(ForAll([x], a0[x] == If(x == Foo.foo, True, False)))
    s.add(ForAll([x], a1[x] == True))
    s.add(IsSubset(a1, a0))
    assert s.check() == unsat