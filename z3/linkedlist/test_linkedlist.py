from z3 import *

def test_reduce_on_linked_list():
    linkedlist = Datatype('linkedlist')
    linkedlist.declare('end')
    linkedlist.declare('cons', ('car', IntSort()), ('cdr', linkedlist))
    linkedlist = linkedlist.create()
    cons = linkedlist.cons
    car = linkedlist.car
    cdr = linkedlist.cdr
    end = linkedlist.end
    is_end = linkedlist.is_end
    a = Array('a', linkedlist, IntSort())
    b = cons(1, cons(2, cons(3, cons(4, cons(5, end)))))
    s = Solver()
    x = Const('x', linkedlist)
    s.add(a == Lambda([x], If(is_end(x), 0, car(x) + a[cdr(x)])))
    s.push()
    s.add(a[b] == 15)
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(a[b] == 16)
    assert s.check() == unsat

def test_accessor():
    maybe = Datatype('maybe')
    maybe.declare('int', ('i', IntSort()))
    maybe.declare('never')
    maybe = maybe.create()
    linkedlist = Datatype('linkedlist')
    linkedlist.declare('end')
    linkedlist.declare('cons', ('car', IntSort()), ('cdr', linkedlist))
    linkedlist = linkedlist.create()
    cons = linkedlist.cons
    car = linkedlist.car
    cdr = linkedlist.cdr
    end = linkedlist.end
    is_end = linkedlist.is_end
    a = Array('a', IntSort(), ArraySort(linkedlist, maybe))
    b = cons(1, cons(2, cons(3, cons(4, cons(5, end)))))
    s = Solver()
    x = Const('x', linkedlist)
    y = Const('y', IntSort())
    s.add(a == Lambda([y],
        Lambda([x],
            If(Or(is_end(x), y < 0),
                maybe.never,
                If(y == 0,
                maybe.int(car(x)),
                a[y-1][cdr(x)])))))
    s.push()
    s.add(a[0][b] == maybe.int(1))
    assert s.check() == sat
    s.pop()
    s.push()
    s.add(a[0][b] == maybe.int(100))
    assert s.check() == unsat
    s.pop()
    s.push()
    s.add(a[100][b] == maybe.never)
    assert s.check() == sat