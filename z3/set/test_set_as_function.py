from z3 import *

def test_set_as_successor_function():
    pair, mk_pair, (first, second) = TupleSort("pair", [IntSort(), IntSort()])
    successor_function = Const('successor_function', SetSort(pair))
    s = Solver()
    x = Const('x', pair)
    s.add(successor_function == Lambda([x], If(first(x) + 1 == second(x), True, False)))
    assert s.check() == sat
    # now we prove it is a function
    a, b = Consts('a b', pair)
    # these constraints will force it to be unsat
    s.add(first(a) == first(b))
    s.add(a != b)
    s.add(successor_function[a])
    s.add(successor_function[b])
    assert s.check() == unsat