from operator import mul, add, mod, eq, sub
from functools import partial
from fn.uniform import reduce, map, filter
from fn.iters import nth
from fn.op import flip
from fn import F, _
import hypothesis


def falsify(name, *args):
    print(name + ": ")
    try:
        print(hypothesis.falsify(*args))
    except Exception as e:
        print(e)


# recursion
def fac(n):
    if n <= 0:
        return 1
    else:
        return n * fac(n - 1)


# higher order
def fac1(n):
    return reduce(mul, range(1, n + 1), 1)


falsify('fac vs fac1', lambda n: not n < 50 or fac(n) == fac1(n), int)
# check only for n < 50


# first class
def mul2(x, y):
    return x * y


mul3 = lambda x, y: x * y


class MulClass(object):

    def __call__(self, x, y):
        return x * y


mul4 = MulClass()


falsify('mul vs mul2', lambda x, y: mul(x, y) == mul2(x, y), int, int)
falsify('mul2 vs mul3', lambda x, y: mul2(x, y) == mul3(x, y), int, int)
falsify('mul3 vs mul4', lambda x, y: mul3(x, y) == mul4(x, y), int, int)


# higher order cont
def reduce1(f, xs, start):
    r = start
    for x in xs:
        r = f(x, r)
    return r


# recursion again
def reduce2(f, xs, start):
    if xs:
        return f(xs[0], reduce2(f, xs[1:], start))
    else:
        return start


def reduce3(f, xs, accumulator):
    if xs:
        return reduce3(f, xs[1:], f(xs[0], accumulator))
    else:
        return accumulator


falsify('reduce vs reduce1',
        lambda xs, s: reduce(add, xs, s) == reduce1(add, xs, s), [int], int)
falsify('reduce1 vs reduce2',
        lambda xs, s: reduce1(add, xs, s) == reduce2(add, xs, s), [int], int)
falsify('reduce2 vs reduce3',
        lambda xs, s: reduce2(add, xs, s) == reduce3(add, xs, s), [int], int)


# higher order cont
def doubles(xs):
    return map(lambda x: x * 2, xs)


falsify('doubles',
        lambda xs: not xs or nth(doubles(xs), 0) == xs[0] * 2, [int])


# partial application
def doubles1(xs):
    return map(partial(mul, 2), xs)


def doubles2(xs):
    return map(F(mul, 2), xs)


falsify('doubles vs double1',
        lambda xs: list(doubles(xs)) == list(doubles1(xs)), [int])
falsify('doubles1 vs double2',
        lambda xs: list(doubles1(xs)) == list(doubles2(xs)), [int])


# higher order cont
def map1(f, xs):
    r = []
    for x in xs:
        r.append(f(x))
    return r


# recursion cont
def map2(f, xs):
    if xs:
        return [f(xs[0])] + map2(f, xs[1:])  # super bad
    else:
        return []


# list comprehension
def map3(f, xs):
    return [f(x) for x in xs]


falsify('map vs map1',
        lambda xs: list(map(F(mul, 2), xs)) == map1(F(mul, 2), xs), [int])
falsify('map1 vs map2',
        lambda xs: map1(F(mul, 2), xs) == map2(F(mul, 2), xs), [int])
falsify('map2 vs map3',
        lambda xs: map2(F(mul, 2), xs) == map3(F(mul, 2), xs), [int])


# higher order cont
def double_evens(xs):
    return doubles(filter(lambda x: x % 2 == 0, xs))


def double_evens1(xs):
    return doubles(filter(_ % 2 == 0, xs))


def compose(f, g):
    return lambda x: f(g(x))


# point free (mostly)
def double_evens2(xs):
    return doubles(filter(F(eq, 0) << F(flip(mod), 2), xs))


def even(x):
    return x % 2 == 0


def flip1(f):
    return lambda x, y: f(y, x)


falsify('flip1', lambda x, y: flip1(sub)(y, x) == sub(x, y), int, int)


even1 = F(flip(mod), 2) >> F(eq, 0)


def double_evens3(xs):
    return doubles(filter(even1, xs))


double_evens4 = F(filter, even1) >> doubles


falsify('double_evens vs double_evens1',
        lambda xs: list(double_evens(xs)) == list(double_evens1(xs)), [int])
falsify('double_evens1 vs double_evens2',
        lambda xs: list(double_evens1(xs)) == list(double_evens2(xs)), [int])
falsify('double_evens2 vs double_evens3',
        lambda xs: list(double_evens2(xs)) == list(double_evens3(xs)), [int])
falsify('double_evens3 vs double_evens4',
        lambda xs: list(double_evens3(xs)) == list(double_evens4(xs)), [int])


sum_double_evens = double_evens4 >> sum


assert sum_double_evens(range(5)) == 12


# higher order cont.
def filter1(pred, xs):
    r = []
    for x in xs:
        if pred(x):
            r.append(x)
    return r


def filter2(pred, xs):
    if xs:
        x = xs[0]
        if pred(x):
            return [x] + filter2(pred, xs[1:])
        else:
            return filter2(pred, xs[1:])
    else:
        return []


def filter3(pred, xs):
    return [x for x in xs if pred(x)]


def filter4(pred, xs):
    return reduce(lambda ys, y: ys + [y] if pred(y) else ys, xs, [])
    # Needs a different data type to be in O(n). Or at least an append which
    # returns the list. Better would be a list which allows to create a new
    # list with a given value as head and a given list as tail.


falsify('filter vs filter1',
        lambda xs: list(filter(even, xs)) == filter1(even, xs), [int])
falsify('filter1 vs filter2',
        lambda xs: filter1(even, xs) == filter2(even, xs), [int])
falsify('filter2 vs filter3',
        lambda xs: filter2(even, xs) == filter3(even, xs), [int])
falsify('filter3 vs filter4',
        lambda xs: filter3(even, xs) == list(filter4(even, xs)), [int])


def map4(f, xs):
    return reduce(lambda ys, y: ys + [f(y)], xs, [])


falsify('map3 vs map4',
        lambda xs: map3(F(mul, 2), xs) == map4(F(mul, 2), xs), [int])


fac2 = F(flip(F(reduce, mul)), 1) << F(range, 1) << F(add, 1)


falsify('fac1 vs fac2', lambda n: not n < 50 or fac1(n) == fac2(n), int)
