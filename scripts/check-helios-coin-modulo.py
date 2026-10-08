#!/usr/bin/env python3
"""Independent composed loader/division traces against supplied coins and integer modulo."""
import contextlib
import io
import itertools
import json
from pathlib import Path
import random
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    loader = runpy.run_path(str(Path(__file__).with_name('check-helios-coin-word-loader.py')))
    division = runpy.run_path(str(Path(__file__).with_name('check-helios-binary-modulo.py')))


def execute(bits, q, mutant=None):
    n = len(bits)
    saved = division['digits'](q)
    sentinel = [True, False, True]
    loaded = loader['execute']([True]*n, bits+sentinel, saved)
    phase, ports, used, before, charge = loaded
    assert phase is None and used == n and before == 4*n+2
    assert ports[:3] == [[], [], []] and ports[4] == saved
    raw = ports[3]
    if mutant == 'wrong_input_port':
        raw = ports[2]
    rem, modulus, raw, pending, after = division['driver'](raw, q)
    if mutant == 'restart_loader':
        used += 1
    final = [rem, modulus, [], [], [], [], raw, pending]
    return final, used, before+after+1, charge+32*(after+1)


def check(bits, q, mutant=None):
    n = len(bits)
    state, used, ticks, charge = execute(bits, q, mutant)
    expected = division['digits'](division['value'](bits) % q)
    assert state == [expected, division['digits'](q), [], [], [], [], [], []]
    assert used == n
    bound = n*(8*q.bit_length()+13)+3
    assert ticks <= 4*n+2+bound
    assert charge <= 15*n+9+32*bound


for mutant in ['wrong_input_port', 'restart_loader']:
    try:
        check([False, True], 3, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant '+mutant)
count = 0
for n in range(7):
    for bits in itertools.product([False, True], repeat=n):
        for q in range(1, 17):
            check(list(bits), q)
            count += 1
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(250):
        check([bool(rng.randrange(2)) for _ in range(rng.randrange(65))], rng.randrange(1, 4097))
print(json.dumps(dict(exhaustive=count, seeded=750, seeds=[7,19,41], width=[0,64],
    modulus=[1,4096], failures=0, gaveUp=0,
    detected_mutants=['wrong_input_port','restart_loader'],
    charge_note='division uses proved per-statement upper bound 32, not measured exact local charge'),indent=2))
