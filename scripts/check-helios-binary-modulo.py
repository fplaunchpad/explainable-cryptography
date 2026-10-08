#!/usr/bin/env python3
"""Executed long-division driver against independent integer modulo."""
import contextlib
import io
import itertools
import json
from pathlib import Path
import random
import runpy

# Reuse the already validated subtraction interpreter, retaining its own checks.
with contextlib.redirect_stdout(io.StringIO()):
    sub = runpy.run_path(str(Path(__file__).with_name('check-helios-binary-subtract.py')))


def value(word):
    return int(''.join('1' if b else '0' for b in reversed(word)) or '0', 2)


def digits(n):
    return [x == '1' for x in reversed(bin(n)[2:])] if n else []


def driver(word, q, mutant=None):
    raw, pending, remainder, modulus = list(word), [], [], digits(q)
    steps = 0
    while raw:
        pending.insert(0, raw.pop(0))
        steps += 1
    steps += 1
    if mutant == 'skip_reverse':
        pending.reverse()
    while pending:
        bit = pending.pop(0)
        steps += 1
        if remainder or bit:
            remainder.insert(0, bit)
        steps += 1
        _, state, used = sub['machine'](remainder, modulus)
        steps += used
        assert state[:5] == ([], modulus, [], [], [])
        out, temporary, remainder = list(state[5]), [], []
        while out:
            temporary.insert(0, out.pop(0))
            steps += 1
        steps += 1
        while temporary:
            remainder.insert(0, temporary.pop(0))
            steps += 1
        steps += 1
        if mutant == 'one_transfer':
            remainder.reverse()
        assert value(remainder) < q
    steps += 1
    return remainder, modulus, raw, pending, steps


def check(word, q, mutant=None):
    r, mod, raw, pending, steps = driver(word, q, mutant)
    assert (r, mod, raw, pending) == (digits(value(word) % q), digits(q), [], [])
    assert steps <= len(word) * (8 * q.bit_length() + 13) + 2


for mutant, word, q in [('skip_reverse', [False, True, True], 5),
                         ('one_transfer', [False, True], 3)]:
    try:
        check(word, q, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant ' + mutant)
words = [list(w) for n in range(9) for w in itertools.product([False, True], repeat=n)]
for word in words:
    for q in range(1, 33):
        check(word, q)
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(500):
        word = [bool(rng.randrange(2)) for _ in range(rng.randrange(129))]
        check(word, rng.randrange(1, 65537))
print(json.dumps({'exhaustive_cases': len(words) * 32, 'random_cases': 1500,
                  'seeds': [7, 19, 41], 'raw_width': [0, 128],
                  'modulus': [1, 65536], 'mutants_detected': ['skip_reverse', 'one_transfer'],
                  'failures': 0, 'gaveUp': 0}, indent=2))
