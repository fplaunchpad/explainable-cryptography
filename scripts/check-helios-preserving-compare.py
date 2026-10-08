#!/usr/bin/env python3
"""Preserved-query machine versus tuple equality and original snapshots."""
import itertools
import json


def machine(left, right, mutant=None):
    query, candidate, scratch = list(left), list(right), []
    steps = 0
    while True:
        steps += 1
        a = query.pop(0) if query else None
        if a is not None:
            scratch.insert(0, a)
        b = candidate.pop(0) if candidate else None
        if a is None:
            equal = b is None or mutant == 'ignore_tail'
            break
        if a != b:
            equal = False
            break
    while scratch:
        steps += 1
        a = scratch.pop(0)
        if mutant != 'skip_restore':
            query.insert(0, a)
    steps += 1
    while candidate:
        steps += 1
        candidate.pop(0)
    steps += 1
    return query, candidate, scratch, equal, steps


def check(a, b, mutant=None):
    q, c, s, eq, fuel = machine(a, b, mutant)
    assert (q, c, s, eq) == (list(a), [], [], tuple(a) == tuple(b))
    assert fuel <= 2*len(a)+len(b)+3


for mutant, a, b in [('skip_restore', [True, False], [True, True]),
                      ('ignore_tail', [], [False])]:
    try:
        check(a, b, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant: '+mutant)
words = [w for n in range(7) for w in itertools.product([False, True], repeat=n)]
for a in words:
    for b in words:
        check(a, b)
print(json.dumps(dict(cases=len(words)**2, max_word_length=6,
                     failures=0, gaveUp=0, detected_mutants=2), indent=2))
