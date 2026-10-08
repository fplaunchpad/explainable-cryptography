#!/usr/bin/env python3
"""Eight-stack lookup composition checked against plain association lists."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    entry = runpy.run_path('scripts/check-helios-cache-entry.py')
    record = runpy.run_path('scripts/check-helios-record-parser.py')
base = entry['field']
compare = entry['key']['compare']


def entry_step(t):
    # Inner logical input/output/archive rotate onto physical output/archive/input.
    local = [t[3], t[1], t[2], t[5], t[4], t[0]]
    steps = 0
    for expected in [True, True, False, False, True]:
        steps += 1
        got = local[0].pop(0) if local[0] else None
        if got != expected:
            return None, steps
    ok, n = base['field'](local)
    steps += n+1
    if not ok:
        return None, steps
    query, candidate, scratch, matched, n = compare['machine'](t[6], local[3])
    t[6][:], local[3][:], local[2][:] = query, candidate, scratch
    steps += n+2  # key finish, entry answer dispatch
    ok, n = base['field'](local)
    steps += n+1
    return (matched if ok and not local[0] else None), steps


def machine(query, word, mutant=None):
    t = [list(word), [], [], [], [], [], list(query), []]
    steps = 0
    while t[0]:
        t[2].insert(0, t[0].pop(0)); steps += 1
    steps += 1
    while t[2]:
        b = t[2].pop(0); t[0].insert(0, b)
        if mutant != 'skip_copy':
            t[7].insert(0, b)
        steps += 1
    steps += 2  # copy halt and caller dispatch
    ok, n = record['count_prefix'](t)
    steps += n+1
    if not ok:
        return None, t, steps
    while t[4]:
        steps += 1
        ok, n = base['field'](t)
        steps += n+1
        if not ok:
            return None, t, steps
        matched, n = entry_step(t)
        steps += n+1
        if matched is None:
            return None, t, steps
        if matched:
            return (True, list(t[5])), t, steps
        if mutant == 'first_only':
            return (False, []), t, steps
        if mutant == 'lose_query':
            t[6].clear()
        while t[5]:
            t[5].pop(0); steps += 1
        steps += 1
        ok, n = base['decrement'](t)
        steps += n+1
        assert ok
    steps += 1
    return ((False, []) if not t[0] else None), t, steps


def enc(n):
    return [True]*n.bit_length()+[False]+base['bits'](n)


def encode(entries):
    words = [entry['record'](k, v) for k, v in entries]
    return enc(len(words))+sum((enc(len(w))+w for w in words), [])


def check(query, entries, mutant=None):
    word = encode(entries)
    actual, t, steps = machine(query, word, mutant)
    expected = next(((True, list(v)) for k, v in entries if tuple(k) == tuple(query)), (False, []))
    assert actual == expected and t[6] == list(query) and t[7] == word
    # Conservative raw-length bound, independent of prime-specific codec bounds.
    L = len(word)
    assert steps <= 10*(L+1)**3+2*(L+1)*len(query)


first, second = ([False], [True]), ([True], [False, True])
for mutant, query, entries in [('skip_copy', [], []),
                               ('first_only', [True], [first, second]),
                               ('lose_query', [True], [first, second])]:
    try:
        check(query, entries, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant: '+mutant)
keys = [[], [False], [True], [False, True]]
answers = [[], [False], [True, False]]
queries = keys+[[True, True]]
cases = 0
for n in range(4):
    for selected in itertools.permutations(keys, n):
        for values in itertools.product(answers, repeat=n):
            for query in queries:
                check(query, list(zip(selected, values)))
                cases += 1
# Directed malformed framing: zero count with trailing data, absent entry,
# malformed inner pair, and missing answer on a nonmatching key.
malformed = [[False, True], enc(1), enc(1)+enc(1)+[False]]
inner = enc(2)+enc(0)
malformed.append(enc(1)+enc(len(inner))+inner)
for word in malformed:
    out, t, _ = machine([True], word)
    assert out is None and t[6] == [True] and t[7] == word
print(json.dumps(dict(canonical_cases=cases, malformed_cases=len(malformed),
                     failures=0, gaveUp=0, detected_mutants=3, max_entries=3), indent=2))
