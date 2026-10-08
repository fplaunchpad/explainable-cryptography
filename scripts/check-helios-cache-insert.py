#!/usr/bin/env python3
"""Guarded nine-stack insertion versus independent ordered association lists."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    lookup = runpy.run_path('scripts/check-helios-cache-lookup.py')
    writer = runpy.run_path('scripts/check-helios-frame-writer.py')
    parser = runpy.run_path('scripts/check-helios-nat-parser-machine.py')


def machine(key, answer, word, mutant=None):
    found, t, steps = lookup['machine'](key, word)
    t.append(list(answer))
    steps += 1  # guarded return from lookup
    if found is None:
        return None, t, steps
    if found[0] and not (mutant == 'insert_on_hit' or
                         (mutant == 'same_answer' and list(found[1]) == list(answer))):
        return False, t, steps
    if found[0]:
        for k in range(6):
            t[k] = []
    assert t[:6] == [[], [], [], [], [], []]
    begin = steps
    parsed, cost = parser['machine'](t[7])
    assert parsed is not None
    t[4], t[7] = list(parsed[0]), list(parsed[1])
    old_width = len(t[4])
    steps += cost+1
    if mutant != 'count':
        steps += writer['increment'](t[4], t[2])
    steps += 1
    new_width = len(t[4])

    def copy(src):
        nonlocal steps
        while t[src]:
            t[2].insert(0, t[src].pop(0)); steps += 1
        steps += 1
        while t[2]:
            b = t[2].pop(0)
            t[src].insert(0, b); t[0].insert(0, b); steps += 1
        steps += 2  # copier halt and dispatch

    def frame(src, dst):
        nonlocal steps
        assert t[1] == t[2] == t[5] == []
        local, cost = writer['write'](t[src], t[dst])
        t[src], t[1], t[2], t[dst], t[5] = local
        steps += cost+1

    copy(8 if mutant != 'fields' else 6)
    frame(0, 3)
    copy(6 if mutant != 'fields' else 8)
    frame(0, 3)
    for b in [True, False, False, True, True]:
        t[3].insert(0, b)
    steps += 1
    entry_length = len(t[3])
    if mutant == 'tail':
        t[7] = []
    frame(3, 7)
    while t[4]:
        t[2].insert(0, t[4].pop(0)); t[1].insert(0, True); steps += 1
    steps += 1
    while t[2]:
        t[7].insert(0, t[2].pop(0)); steps += 1
    t[7].insert(0, False); steps += 1
    while t[1]:
        t[1].pop(0); t[7].insert(0, True); steps += 1
    steps += 2  # prefix halt and insertion halt
    field_cost = lambda L: L*(2*L.bit_length()+5)+3*L.bit_length()+5
    bound = (5*old_width+3*new_width+2*len(key)+2*len(answer)+
             field_cost(len(key))+field_cost(len(answer))+field_cost(entry_length)+21)
    assert steps-begin <= bound
    assert t[:6] == [[], [], [], [], [], []]
    return True, t, steps


def check(key, answer, entries, mutant=None):
    word = lookup['encode'](entries)
    found = any(tuple(k) == tuple(key) for k, _ in entries)
    expected = entries if found else [(key, answer)]+entries
    inserted, t, _ = machine(key, answer, word, mutant)
    assert inserted == (not found)
    assert t[6] == list(key) and t[8] == list(answer) and t[7] == lookup['encode'](expected)


for mutant, key, answer, entries in [
        ('count', [], [True], []),
        ('fields', [False], [True], []),
        ('tail', [True], [False], [([False], [True])]),
        ('insert_on_hit', [False], [True], [([False], [False])]),
        ('same_answer', [False], [False], [([False], [False])])]:
    try:
        check(key, answer, entries, mutant)
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
            for key in queries:
                for answer in answers:
                    check(key, answer, list(zip(selected, values)))
                    cases += 1
for word in lookup['malformed']:
    result, t, _ = machine([True], [False, True], word)
    assert result is None and t[6] == [True] and t[7] == word and t[8] == [False, True]
print(json.dumps(dict(canonical_cases=cases, malformed_cases=len(lookup['malformed']),
                     max_entries=3, detected_mutants=5, failures=0, gaveUp=0), indent=2))
