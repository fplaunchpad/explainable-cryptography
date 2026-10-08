#!/usr/bin/env python3
"""Independent sampler and writer execution on the same eight stack ports."""
import contextlib
import io
import itertools
import json
from pathlib import Path
import random
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    sampler = runpy.run_path(str(Path(__file__).with_name('check-helios-coin-modulo.py')))


def execute(coins, q, mutant=None):
    words, used, ticks, charge = sampler['execute'](coins, q)
    before = ticks
    if mutant == 'fresh_load':
        words[0] = []
    # Continue from the actual remainder port; no decode/re-encode at the boundary.
    while words[0]:
        words[3].insert(0, words[0].pop(0))
        words[2].insert(0, True)
        ticks += 1
    ticks += 1
    while words[3]:
        words[5].insert(0, words[3].pop(-1 if mutant == 'reverse' else 0))
        ticks += 1
    words[5].insert(0, False)
    ticks += 1
    while words[2]:
        words[2].pop(0)
        words[5].insert(0, True)
        ticks += 1
    ticks += 1
    if mutant == 'after_halt':
        used += 1
    return words, used, ticks, charge+32*(ticks-before)


def check(coins, q, mutant=None):
    words, used, ticks, charge = execute(coins, q, mutant)
    raw = sum(int(b) << i for i, b in enumerate(coins))
    n = raw % q
    expected = [True]*n.bit_length()+[False]+[bool((n >> i)&1) for i in range(n.bit_length())]
    modulus = [bool((q >> i)&1) for i in range(q.bit_length())]
    assert words == [[], modulus, [], [], [], expected, [], []]
    w = len(coins)
    division = w*(8*q.bit_length()+13)+3
    writer = 3*(q-1).bit_length()+3
    assert used == w
    assert ticks <= 4*w+2+division+writer
    assert charge <= 15*w+9+32*division+32*writer


for mutant in ['fresh_load','reverse','after_halt']:
    try:
        check([False,True],3,mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant '+mutant)
count=0
for w in range(7):
    for coins in itertools.product([False,True],repeat=w):
        for q in range(1,17):
            check(list(coins),q)
            count+=1
for seed in [7,19,41]:
    rng=random.Random(seed)
    for _ in range(250):
        check([bool(rng.randrange(2)) for _ in range(rng.randrange(65))],rng.randrange(1,4097))
print(json.dumps(dict(exhaustive=count,seeded=750,seeds=[7,19,41],width=[0,64],modulus=[1,4096],
    detected_mutants=['fresh_load','reverse','after_halt'],failures=0,gaveUp=0,
    charge_note='division/writer use conservative proved per-statement bound 32'),indent=2))
