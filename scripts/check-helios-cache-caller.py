#!/usr/bin/env python3
"""Adaptive caller fixtures: executed words versus independent integer/map semantics."""
import contextlib
import io
import itertools
import json
import random
import runpy
from pathlib import Path

with contextlib.redirect_stdout(io.StringIO()):
    cache = runpy.run_path('scripts/check-helios-cache-coins.py')
    prepared = runpy.run_path('scripts/check-helios-prepared-scalar.py')
    framed = runpy.run_path('scripts/check-helios-cache-sampler-frame.py')
old, scalar = cache['old'], cache['scalar']
keys = [[], [False], [True]]


def read(word):
    width = word.index(False)
    digits = word[width+1:]
    assert len(digits) == width
    assert not digits or digits[-1]
    return sum(int(b) << i for i, b in enumerate(digits))


def actual(entries, log, tape, slack, mutant=None):
    word, logged = old['encode_cache'](entries), old['log_append']['encode'](log)
    state, remaining, _, _ = prepared['execute'](
        True, prepared['prep']['encode'](slack, 1, []), tape)
    used = len(tape)-len(remaining)
    u = read(state[5])
    first = keys[u]
    answers = []
    for index in range(3):
        key = first if index < 2 else keys[1 + answers[0] % 2]
        if mutant == 'reset' and index == 1:
            word = old['encode_cache']([])
        found, _, _ = old['cache_read']['machine'](key, word)
        if found[0]:
            value, word, logged, cost = cache['driver'](
                key, word, logged, tape[used:], 4+slack,
                'hit_coin' if mutant == 'hit_coin' else None)
        else:
            record = prepared['prep']['encode'](slack, 11, [])
            state, retained, remaining, _, _ = framed['execute'](record, key, word, logged, tape[used:])
            assert retained == [key, word, logged, record]
            value = state[5]
            cost = len(tape)-used-len(remaining)
            ok, inserted, _ = old['insertion']['machine'](key, value, word)
            assert ok
            word = inserted[7]
            logged = old['log_append']['machine'](key, logged)[0]
        used += cost
        answers.append(read(value))
    if mutant == 'drop_log':
        logged = old['log_append']['encode']([])
    return (u, *answers), word, logged, tape[used:]


def expected(entries, log, tape, slack):
    entries, log = list(entries), list(log)
    used = 2+slack
    u = sum(int(b) << i for i, b in enumerate(tape[:used])) % 2
    first, answers = keys[u], []
    for index in range(3):
        key = first if index < 2 else keys[1 + answers[0] % 2]
        found = next((value for k, value in entries if k == key), None)
        if found is None:
            found = sum(int(b) << i for i, b in enumerate(tape[used:used+4+slack])) % 11
            used += 4+slack
            entries.insert(0, (key, found))
            log.append(key)
        answers.append(found)
    return ((u, *answers), old['encode_cache'](entries),
            old['log_append']['encode'](log), tape[used:])


for mutant in ['hit_coin', 'reset', 'drop_log']:
    args = ([], [[True]], [False, True, False, True, True, False] + [True]*12, 0)
    assert actual(*args, mutant) != expected(*args), 'undetected ' + mutant
count = 0
for entries, log, bits in itertools.product(
        [[], [([], 3)], [([False], 6), ([True], 5)]],
        [[], [[True]]], itertools.product([False, True], repeat=10)):
    args = (entries, log, list(bits)+[True, False], 0)
    assert actual(*args) == expected(*args)
    count += 1
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(100):
        slack = rng.randrange(4)
        args = ([], [rng.choice(keys)], [rng.choice([False, True]) for _ in range(30)], slack)
        assert actual(*args) == expected(*args)
result = dict(exhaustive=count, seeded=300, seeds=[7,19,41], modulus=11,
              max_slack=3, requests='one uniform and three adaptive hashes',
              mutants=['hit_coin','reset','drop_log'], failures=0, gaveUp=0)
Path('tmp/concrete-helios/cache-caller-fixtures.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
