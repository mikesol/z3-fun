from z3 import *

def test_disjoint_sum():
    '''
    Disjoint sum is just a datatype that creates constructors and accessors
    for a primitive type.
    '''
    int_and_string, ((int_c, int_e), (string_c, string_e)) = DisjointSum('int_and_string', [IntSort(), StringSort()])
    c = int_c(531) # does not matter what this int is (I think)
    assert c.sort() == int_and_string
    s = Solver()
    s.add(int_e(c) < 0)
    s.add(int_e(c) > 10)
    assert s.check() == unsat