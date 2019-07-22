from z3 import *
def test_functions_are_mutually_exclusive():
    MaybeInt = Datatype('MaybeInt')
    MaybeInt.declare('int', ('i', IntSort()))
    MaybeInt.declare('never')
    MaybeInt = MaybeInt.create()
    a0, a1, a2, a3, a4, a5, a6, proof = Consts('a0 a1 a2 a3 a4 a5 a6 proof', MaybeInt)
    arr0 = Array('arr0', MaybeInt, MaybeInt)
    arr1 = Array('arr1', MaybeInt, MaybeInt)
    arr2 = Array('arr2', MaybeInt, MaybeInt)
    arr3 = Array('arr3', MaybeInt, MaybeInt)
    arr4 = Array('arr4', MaybeInt, MaybeInt)
    arr5 = Array('arr5', MaybeInt, MaybeInt)
    arr6 = Array('arr6', MaybeInt, MaybeInt)
    a1q, a2q, a3q = Ints('a1q a2q a3q')
    s = Solver()
    s.add(arr0 == Lambda([a0], a0)) # change to arr0[a0] == a0
    s.add(a1q == 0)
    s.add(a2q == 0)
    s.add(a3q == 1)
    # less than 0
    s.add(arr1 == Lambda([a1], If(And(MaybeInt.is_int(a1), MaybeInt.i(a1) < a1q), a1, MaybeInt.never)))
    # greater than or equal to 0
    s.add(arr2 == Lambda([a2], If(And(MaybeInt.is_int(a2), MaybeInt.i(a2) >= a2q), a2, MaybeInt.never)))
    # less than 1
    s.add(arr3 == Lambda([a3], If(And(MaybeInt.is_int(a3), MaybeInt.i(a3) < a3q), a3, MaybeInt.never)))
    # 1 and 2 together
    s.add(arr4 == Lambda([a4], If(arr1[a4] != MaybeInt.never, arr1[a4], arr2[a4])))
    # maximally captures arr2 and arr3 overlap
    s.add(arr5 == Lambda([a5], If(
        And(arr2[a5] != MaybeInt.never, arr3[a5] != MaybeInt.never),
        arr2[a5],
        If(
            arr2[a5] != MaybeInt.never,
            arr2[a5],
            If(arr3[a5] != MaybeInt.never,
            arr3[a5],
            MaybeInt.never))
    )))
    # minimally captures arr2 and arr3 overlap
    s.add(arr6 == Lambda([a6], If(And(arr2[a6] != MaybeInt.never, arr3[a6] != MaybeInt.never), arr3[a6], MaybeInt.never)))
    s.push()
    # arr1 and arr2 are mutually exclusive
    s.add(And(arr1[proof] != MaybeInt.never, arr2[proof] != MaybeInt.never))
    assert s.check() == unsat
    s.pop()
    s.push()
    # arr1 and arr3 overlap at 0, so this will be a place where they both don't equal never
    s.add(And(arr1[proof] != MaybeInt.never, arr3[proof] != MaybeInt.never))
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(arr0 == arr4) # recombination works
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(proof != MaybeInt.never)
    s.add(arr5[proof] == MaybeInt.never)
    assert s.check() == unsat # Because arr5 covers the whole space
    s.pop()
    s.push()
    s.add(proof != MaybeInt.never)
    s.add(proof != MaybeInt.int(0))
    s.add(arr6[proof] != MaybeInt.never)
    assert s.check() == unsat # if proof is neither 0 or never, we can never *not* get never