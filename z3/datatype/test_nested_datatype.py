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
    LIMIT = 1000
    for x in range(LIMIT):
        ndt = Datatype('l%d' % (x + 1))
        ndt.declare('s%d' % (x+1), ('_s%d' % (x+1), SetSort(dts[-1])))
        # wow, ndt works but dts[-1] does not work for tuple!!
        #ndt.declare('p%d' % (x + 1), ('_left%d' % (x + 1), ndt), ('_right%d' % (x + 1), dts[-1]))        
        ndt.declare('s%d' % (x+1), ('_s%d' % (x+1), ArraySort(dts[-1], dts[-1])))
        ndt.declare('o%d' % (x + 1), ('_o%d' % (x + 1), dts[-1]))        
        dts.append(ndt.create())