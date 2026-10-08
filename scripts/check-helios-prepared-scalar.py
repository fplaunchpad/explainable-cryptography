#!/usr/bin/env python3
"""Complete prepared sampler using produced modulus/width ports without reloading them."""
import contextlib
import io
import itertools
import json
import random
import runpy
from pathlib import Path

with contextlib.redirect_stdout(io.StringIO()):
    prep = runpy.run_path('scripts/check-helios-sampler-operands.py')
    old = runpy.run_path('scripts/check-helios-coin-modulo.py')


def execute(mode, raw, tape, mutant=None):
    ok, w, ticks = prep['execute'](mode, raw, [[], [], []])
    charge = 32*ticks+5
    ticks += 1
    if (not ok or w[4]) and mutant != 'bypass_gate':
        return None, tape, ticks, charge
    if mutant == 'wrong_modulus': w[1] = [True]
    _, loaded, used, steps, load_charge = old['loader']['execute'](w[2], tape, w[1])
    w[2], w[4], w[5], w[6], w[1] = loaded
    ticks += steps
    charge += load_charge
    # Continue on the eight real ports. The subtraction interpreter accepts raw digits.
    steps = 0
    while w[6]:
        w[7].insert(0, w[6].pop(0)); steps += 1
    steps += 1
    while w[7]:
        bit = w[7].pop(0); steps += 1
        if w[0] or bit: w[0].insert(0, bit)
        steps += 1
        _, state, sub_steps = old['division']['sub']['machine'](w[0], w[1])
        w[:6] = map(list, state)
        steps += sub_steps
        while w[5]:
            w[3].insert(0, w[5].pop(0)); steps += 1
        steps += 1
        while w[3]:
            w[0].insert(0, w[3].pop(0)); steps += 1
        steps += 1
    steps += 2
    ticks += steps; charge += 32*steps
    steps = 0
    while w[0]:
        w[3].insert(0, w[0].pop(0)); w[2].insert(0, True); steps += 1
    steps += 1
    while w[3]:
        w[5].insert(0, w[3].pop(0)); steps += 1
    w[5].insert(0, False); steps += 1
    while w[2]:
        w[2].pop(0); w[5].insert(0, True); steps += 1
    steps += 1
    ticks += steps; charge += 32*steps
    if mutant == 'extra_coin': used += 1
    return w, tape[used:], ticks, charge


def check(mode, raw, tape, mutant=None):
    w, rest, ticks, charge = execute(mode, raw, tape, mutant)
    ref = prep['reference'](mode, raw)
    if ref is None or ref[2]:
        assert w is None and rest == tape
        return
    slack, q, _ = ref
    width = q.bit_length()+slack
    residue = sum(int(b) << i for i, b in enumerate(tape[:width])) % q
    value = [True]*residue.bit_length()+[False]+prep['bits'](residue)
    assert w == [[], prep['bits'](q), [], [], [], value, [], []]
    assert rest == tape[width:]
    n = q-1 if mode else q
    preparation = slack+5*n.bit_length()+(2*q.bit_length()+10 if mode else 8)
    division = width*(8*q.bit_length()+13)+3
    writer = 3*(q-1).bit_length()+3
    assert ticks <= preparation+1+4*width+2+division+writer
    assert charge <= 32*preparation+5+15*width+9+32*division+32*writer


for mutant in ['bypass_gate','wrong_modulus','extra_coin']:
    raw = prep['encode'](0, 11, [True] if mutant == 'bypass_gate' else [])
    try: check(False, raw, [False, True, True, False, True, False], mutant)
    except AssertionError: pass
    else: raise AssertionError('undetected '+mutant)
count = 0
for mode, n, slack in itertools.product([False, True], range(17), range(3)):
    q = n+1 if mode else n
    width = q.bit_length()+slack
    for tape in itertools.product([False, True], repeat=width):
        check(mode, prep['encode'](slack, n, []), list(tape)+[True, False])
        count += 1
for raw in [[], [True], [False, True, False], [False, False], [False, False, True]]:
    for mode in [False, True]: check(mode, raw, [True, False, True])
for seed in [7,19,41]:
    rng = random.Random(seed)
    for _ in range(100):
        n, slack, mode = rng.randrange(1,4096), rng.randrange(33), bool(rng.getrandbits(1))
        tape = [bool(rng.getrandbits(1)) for _ in range(64)]
        check(mode, prep['encode'](slack,n,[]),tape)
report = dict(exhaustive=count, malformed_directed=10, seeded=300, seeds=[7,19,41],
              mutants=['bypass_gate','wrong_modulus','extra_coin'], failures=0, gaveUp=0,
              charge='derived per-statement upper bounds, not exact measurement')
Path('tmp/concrete-helios/prepared-scalar-fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
