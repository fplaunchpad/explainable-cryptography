#!/usr/bin/env python3
"""Original pair header, actual field/compare stack routines, independent decoder."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    field = runpy.run_path('scripts/check-helios-record-field-step.py')
    compare = runpy.run_path('scripts/check-helios-preserving-compare.py')
HEADER = [True, True, False, False, True]


def machine(query, word, mutant=None):
    tapes = [list(word), [], [], [], [False, True], [True, False, False]]
    steps = 0
    for bit in HEADER:
        steps += 1
        got = tapes[0].pop(0) if tapes[0] else None
        if got != bit and mutant != 'ignore_count':
            return None, list(query), tapes, steps
    ok, n = field['field'](tapes)
    steps += n+1
    if not ok:
        return (False if mutant == 'malformed_miss' else None), list(query), tapes, steps
    q, candidate, scratch, eq, n = compare['machine'](query, tapes[3])
    tapes[3], tapes[2] = candidate, scratch
    return eq, q, tapes, steps+n+1


def reference(query, word):
    # Read canonical binary-natural prefix using an independent index.
    def natural(pos):
        width = 0
        while pos+width < len(word) and word[pos+width]:
            width += 1
        stop = pos+2*width+1
        if stop > len(word):
            return None
        n = sum(int(word[pos+width+1+i])*2**i for i in range(width))
        return (n, stop) if n.bit_length() == width else None
    head = natural(0)
    if head is None or head[0] != 2:
        return None
    length = natural(head[1])
    if length is None or length[0] > len(word)-length[1]:
        return None
    size, pos = length
    return tuple(query) == tuple(word[pos:pos+size]), list(word[pos+size:])


def check(query, word, mutant=None):
    eq, q, tapes, steps = machine(query, word, mutant)
    expected = reference(query, word)
    assert q == list(query) and tapes[4:] == [[False, True], [True, False, False]]
    if expected is None:
        assert eq is None
    else:
        assert (eq, tapes[0]) == expected and not tapes[1] and not tapes[2] and not tapes[3]
    L = len(word)
    assert steps <= 3*L+17+(L+1)*(2*L+4)+2*len(query)


for mutant, query, word in [('ignore_count', [], [False]*6),
                             ('malformed_miss', [], HEADER)]:
    try:
        check(query, word, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant: '+mutant)
queries = [w for n in range(4) for w in itertools.product([False, True], repeat=n)]
raw = 0
for n in range(11):
    for word in itertools.product([False, True], repeat=n):
        for query in queries:
            check(query, word)
            raw += 1
structured = 0
for n in range(6):
    for key in itertools.product([False, True], repeat=n):
        enc = [True]*n.bit_length()+[False]+field['bits'](n)
        for suffix in [[], [False], [True, False, True]]:
            for query in queries:
                check(query, HEADER+enc+list(key)+suffix)
                structured += 1
print(json.dumps(dict(raw=raw, structured=structured, failures=0, gaveUp=0,
                     detected_mutants=2, max_raw_length=10, max_query_length=3), indent=2))
