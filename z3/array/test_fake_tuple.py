from z3 import *

def test_fake_tuple():
    '''
    We can make an array that fakes tuple behavior
    For example, we can set an arbitrary index in the array to the element we want
    from the tuple.
    '''
    foo, mk_foo, (int0, string1, int2) = TupleSort('foo', [IntSort(), StringSort(), IntSort()])
    a = mk_foo(Int('c'), String('f'), Int('q'))
    arr = Array('arr', IntSort(), foo)
    s = Solver()
    s.add(int0(a) == 5)
    s.add(int0(Store(arr, 0, mk_foo(Int('c'), String('f'), Int('q')))[0]) == 5)
    s.add(int0(Store(arr, 0, mk_foo(Int('c'), String('f'), Int('q')))[0]) != int0(a))
    assert s.check() == unsat