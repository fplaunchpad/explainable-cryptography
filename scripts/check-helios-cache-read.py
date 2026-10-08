#!/usr/bin/env python3
"""Decode actual lookup hits in place; preserve query/cache and distinguish zero."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    lookup = runpy.run_path('scripts/check-helios-cache-lookup.py')
    parser = runpy.run_path('scripts/check-helios-nat-parser-machine.py')

def scalar(n):
    width = n.bit_length()
    return [True]*width+[False]+[bool(n & (1 << i)) for i in range(width)]

def encode(entries):
    return lookup['encode']([(k, scalar(a)) for k, a in entries])

def machine(key, word, mutant=None):
    found, t, steps = lookup['machine'](key, word)
    steps += 1
    if found is None:
        return None, t, steps
    if not found[0]:
        return (False, []), t, steps
    assert t[1:4] == [[], [], []]
    parsed, used = parser['machine'](t[5])
    steps += used+1
    if parsed is None or parsed[1]:
        return None, t, steps
    t[3], t[5] = list(parsed[0]), list(parsed[1])
    if mutant == 'skip_decode':
        t[3] = list(found[1])
    if mutant == 'reverse':
        t[3].reverse()
    if mutant == 'lose_cache':
        t[7] = []
    if mutant == 'lose_query':
        t[6] = []
    return (False, []) if mutant == 'zero_miss' and not t[3] else (True, t[3]), t, steps

def check(key, entries, mutant=None):
    word = encode(entries)
    value = next((v for k, v in entries if k == key), None)
    expected = (False, []) if value is None else (True,
        [c == '1' for c in bin(value)[2:][::-1]] if value else [])
    result, t, _ = machine(key, word, mutant)
    assert result == expected and t[6] == key and t[7] == word

for mutant, n in [('skip_decode', 0), ('zero_miss', 0), ('reverse', 6),
                  ('lose_cache', 6), ('lose_query', 6)]:
    try:
        check([True], [([True], n)], mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant '+mutant)
keys = [[], [False], [True], [False, True]]
values = [0, 1, 6]
cases = 0
for n in range(4):
    for selected in itertools.permutations(keys, n):
        for answers in itertools.product(values, repeat=n):
            for key in keys+[[True, True]]:
                check(key, list(zip(selected, answers)))
                cases += 1
malformed = [[], [False, True], [True], [True, False, False]]
for bad in malformed:
    word = lookup['encode']([([True], bad)])
    result, t, _ = machine([True], word)
    assert result is None and t[6] == [True] and t[7] == word
print(json.dumps(dict(cases=cases, malformed_scalar_cases=4, max_entries=3,
                     detected_mutants=5, failures=0, gaveUp=0), indent=2))
