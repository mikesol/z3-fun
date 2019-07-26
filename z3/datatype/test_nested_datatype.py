from z3 import *

def test_nested_datatype():
    l0 = Datatype('l0')
    l0.declare('i', ('_i', IntSort()))
    l0.declare('s', ('_s', StringSort()))
    l0.declare('b', ('_b', BoolSort()))
    l0.declare('r', ('_r', RealSort()))
    l0 = l0.create()
    dts = [l0]
    # anything bigger than 14 and it starts going crazy!
    for x in range(14):
        ndt = Datatype('l%d' % (x + 1))
        ndt.declare('s', ('_s', SetSort(dts[-1])))
        ts, _, _ = TupleSort('l%dt' % (x + 1), [dts[-1], dts[-1]])
        ndt.declare('p', ('_p', ts))
        ndt.declare('o', ('_o', dts[-1]))
        dts.append(ndt.create())