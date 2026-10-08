#!/usr/bin/env python3
"""Guarded binary subtraction against independently computed integer answers."""
import itertools
import json

def value(word):
    return int(''.join('1' if b else '0' for b in reversed(word)) or '0', 2)

def bits(n):
    return [b == '1' for b in reversed(bin(n)[2:])] if n else []

def machine(xs, ys, mutant=None):
    # Physical stacks: left, right, reverse difference, left archive, right archive, output.
    x, y, rev, sx, sy, out = list(xs), list(ys), [], [], [], []
    borrow, steps = False, 0
    while x or y:
        a = x.pop(0) if x else None
        b = y.pop(0) if y else None
        if a is not None:
            sx.insert(0, a)
        if b is not None:
            sy.insert(0, b)
        av, bv = bool(a), bool(b)
        rev.insert(0, av ^ bv ^ borrow)
        borrow = (not av and bv) or (not (av ^ bv) and borrow)
        if mutant == 'drop_borrow':
            borrow = False
        steps += 1
    steps += 1
    while sy:
        y.insert(0, sy.pop(0)); steps += 1
    steps += 1
    if borrow:
        while rev:
            rev.pop(0); steps += 1
        steps += 1
        while sx:
            out.insert(0, sx.pop(0)); steps += 1
        steps += 1
    else:
        while sx:
            sx.pop(0); steps += 1
        steps += 1
        while rev and not rev[0]:
            rev.pop(0); steps += 1
        steps += 1
        while rev:
            out.insert(0, rev.pop(0)); steps += 1
        steps += 1
    if mutant == 'reverse':
        out.reverse()
    if mutant == 'lose_modulus':
        y = []
    if mutant == 'zero_equal':
        borrow = borrow or value(xs) == value(ys)
    if mutant == 'wrap_underflow' and borrow:
        out = bits((value(xs)-value(ys)) % (2**max(len(xs),len(ys))))
    return not borrow, (x, y, rev, sx, sy, out), steps

def check(xs, ys, mutant=None):
    ok, st, steps = machine(xs, ys, mutant)
    a, b = value(xs), value(ys)
    expected = bits(a-b) if a >= b else xs
    assert ok == (a >= b) and st == ([],ys,[],[],[],expected)
    assert steps <= 3*(len(xs)+len(ys))+5

for mutant, a, b in [('drop_borrow',8,1),('reverse',7,1),('lose_modulus',7,1),
                      ('zero_equal',0,0),('wrap_underflow',1,2)]:
    try:
        check(bits(a),bits(b),mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant '+mutant)
words = [list(w) for n in range(7) for w in itertools.product([False,True],repeat=n)]
for a in words:
    for b in words:
        check(a,b)
for width in [7,8,16,65,257]:
    for a,b in [(2**width,1),(1,2**width),(2**width-1,2**width-1),(2**width-1,2**(width-1))]:
        check(bits(a),bits(b))
# Required long-division step: push one new low digit onto canonical remainder,
# suppressing the sole noncanonical zero case, then execute guarded subtraction.
remainder_cases = 0
for q in range(1,65):
    for r in range(q):
        for b in [False,True]:
            loaded = bits(r)
            if loaded or b:
                loaded.insert(0,b)
            _,st,steps = machine(loaded,bits(q))
            assert st == ([],bits(q),[],[],[],bits((2*r+int(b))%q))
            assert steps+1 <= 6*q.bit_length()+9
            remainder_cases += 1
print(json.dumps(dict(cases=len(words)**2,boundary_cases=20,max_raw_width=6,
    max_directed_width=258,remainder_cases=remainder_cases,detected_mutants=5,failures=0,gaveUp=0),indent=2))
