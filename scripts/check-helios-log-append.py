#!/usr/bin/env python3
"""Eight-stack log append versus independent chronological record encoding."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    writer = runpy.run_path('scripts/check-helios-frame-writer.py')
    parser = runpy.run_path('scripts/check-helios-nat-parser-machine.py')

def nat(n):
    width = n.bit_length()
    return [True]*width+[False]+[bool(n & (1 << i)) for i in range(width)]

def encode(words):
    return nat(len(words)) + [b for word in words for b in nat(len(word))+word]

def machine(key, log, mutant=None):
    # src, carry, scratch, out, count, temp, key, body
    t = [[], [], [], [], [], [], list(key), list(log)]
    parsed, steps = parser['machine'](t[7])
    if parsed is None:
        return None, t, steps+1
    t[4], t[7] = list(parsed[0]), list(parsed[1])
    old_size, body_len = len(t[4]), len(t[7])
    steps += 1
    if mutant != 'count':
        steps += writer['increment'](t[4], t[2])
    steps += 1
    while t[6]:
        t[2].insert(0, t[6].pop(0)); steps += 1
    steps += 1
    while t[2]:
        b = t[2].pop(0)
        t[0].insert(0, b)
        if mutant != 'lose_key':
            t[6].insert(0, b)
        steps += 1
    steps += 2
    w, used = writer['write'](t[0], [])
    t[0], t[1], t[2], t[3], t[5] = w
    if mutant == 'empty' and not key:
        t[3] = []
    steps += used+1
    if mutant == 'prepend':
        old = list(t[7])
    while t[7]:
        t[0].insert(0, t[7].pop(0)); steps += 1
    steps += 1
    while t[0]:
        t[3].insert(0, t[0].pop(0 if mutant != 'reverse' else -1)); steps += 1
    steps += 1
    if mutant == 'prepend':
        t[3] = nat(len(key))+list(key)+old
    while t[4]:
        t[2].insert(0, t[4].pop(0)); t[1].insert(0, True); steps += 1
    steps += 1
    while t[2]:
        t[3].insert(0, t[2].pop(0)); steps += 1
    t[3].insert(0, False); steps += 1
    while t[1]:
        t[1].pop(0); t[3].insert(0, True); steps += 1
    steps += 2
    return t[3], t, steps

def check(words, key, mutant=None):
    word, t, steps = machine(key, encode(words), mutant)
    assert word == encode(words+[key])
    assert t == [[], [], [], word, [], [], key, []]
    n, k = len(words), len(key)
    body = sum(len(nat(len(w)))+len(w) for w in words)
    j = k*(2*k.bit_length()+5)+3*k.bit_length()+5
    assert steps <= 5*n.bit_length()+3*(n+1).bit_length()+2*k+j+2*body+17

for mutant, words, key in [('count', [], []), ('prepend', [[False]], [True]),
                          ('reverse', [[False, True]], [True]),
                          ('lose_key', [], [True]), ('empty', [], [])]:
    try:
        check(words, key, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant '+mutant)
keys = [[], [False], [True], [False, True], [True, False]]
cases = 0
for n in range(5):
    for words in itertools.product(keys, repeat=n):
        for key in keys:
            check(list(words), key)
            cases += 1
for n in [7, 8, 15, 16, 31, 32]:
    check([[False, True]]*n, [True, False])
def prefix(counter, suffix, mutant=None):
    counter, scratch, marks, out = list(counter), [], [], list(suffix)
    steps = 0
    while counter:
        scratch.insert(0, counter.pop(0)); marks.insert(0, True); steps += 1
    steps += 1
    while scratch:
        out.insert(0, scratch.pop(0 if mutant != 'reverse' else -1)); steps += 1
    if mutant != 'delimiter':
        out.insert(0, False)
    steps += 1
    while marks:
        marks.pop(0); out.insert(0, True); steps += 1
    return out, steps+1

for mutant in ['reverse', 'delimiter']:
    result, _ = prefix([False, True, True], [True, False], mutant)
    assert result != nat(6)+[True, False]
scalar_cases = 0
for n in list(range(33))+[2**16-1, 2**65-1, 2**257-1]:
    digits = [c == '1' for c in bin(n)[2:][::-1]] if n else []
    for suffix in [[], [False, True], [True, False]]:
        result, steps = prefix(digits, suffix)
        assert result == nat(n)+suffix
        assert steps == 3*n.bit_length()+3
        scalar_cases += 1
print(json.dumps(dict(cases=cases, boundary_cases=6, max_entries=32,
                     scalar_prefix_cases=scalar_cases, scalar_prefix_mutants=2,
                     detected_mutants=5, failures=0, gaveUp=0), indent=2))
