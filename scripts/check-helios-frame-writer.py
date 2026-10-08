#!/usr/bin/env python3
"""Independent five-stack framing execution and literal integer encoding oracle."""
import itertools
import json


def bits(n):
    return [bool((n >> i) & 1) for i in range(n.bit_length())]


def encoded(n):
    return [True]*n.bit_length()+[False]+bits(n)


def increment(counter, scratch, mutant=None):
    steps = 0
    while True:
        b = counter.pop(0) if counter else None
        steps += 1
        if b is True and mutant != 'carry':
            scratch.insert(0, False)
        else:
            counter.insert(0, True)
            break
    while scratch:
        counter.insert(0, scratch.pop(0))
        steps += 1
    return steps+1


def write(payload, suffix, mutant=None):
    # input, carry/width, reversed payload/digits, output, binary length
    t = [list(payload), [], [], list(suffix), []]
    steps = 0
    while t[0]:
        t[2].insert(0, t[0].pop(0))
        steps += 1
        steps += increment(t[4], t[1], mutant)
        steps += 1  # return link to collect
    steps += 1
    while t[2]:
        t[3].insert(0, t[2].pop(0 if mutant != 'reverse' else -1))
        steps += 1
    steps += 1
    while t[4]:
        t[2].insert(0, t[4].pop(0))
        t[1].insert(0, True)
        steps += 1
    steps += 1
    while t[2]:
        t[3].insert(0, t[2].pop(0))
        steps += 1
    if mutant != 'delimiter':
        t[3].insert(0, False)
    steps += 1
    while t[1]:
        t[1].pop(0)
        t[3].insert(0, True)
        steps += 1
    steps += 1
    return t, steps


def check(word, suffix, mutant=None):
    t, fuel = write(word, suffix, mutant)
    n = len(word)
    assert t == [[], [], [], encoded(n)+list(word)+list(suffix), []]
    assert fuel <= n*(2*n.bit_length()+5)+3*n.bit_length()+5


for mutant, word in [('carry', [False, True]), ('reverse', [False, True]), ('delimiter', [])]:
    try:
        check(word, [True, False], mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant: '+mutant)
ns = list(range(1025))+[2**k-1 for k in (16,65,257)]
for n in ns:
    c, s = bits(n), []
    fuel = increment(c, s)
    assert c == bits(n+1) and s == [] and fuel <= 2*n.bit_length()+2
cases = 0
for n in range(11):
    for word in itertools.product([False, True], repeat=n):
        for suffix in ([], [False], [True, False, True]):
            check(word, suffix)
            cases += 1
print(json.dumps(dict(increment_cases=len(ns), field_cases=cases, max_payload_length=10,
                     directed_carry_widths=[16,65,257], detected_mutants=3,
                     failures=0, gaveUp=0), indent=2))
