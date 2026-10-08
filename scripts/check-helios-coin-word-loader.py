#!/usr/bin/env python3
"""Independent finite loader interpreter; response lists are the expected output."""
import itertools
import json
import random


def execute(width, answers, modulus, mutant=None, fuel=None):
    stacks = [list(width), [], [], [], list(modulus)]
    phase, ticks, charge, used = 0, 0, 0, 0
    while phase is not None and (fuel is None or ticks < fuel):
        ticks += 1
        if phase == 0:
            present = bool(stacks[0])
            if present:
                stacks[0].pop(0)
            phase = 1 if present or mutant == 'extra_coin' else 3
            charge += 4
        elif phase == 1:
            if used == len(answers):
                return 'excess query'
            charge += 2 + len(stacks[1])
            stacks[1] = [answers[used]]
            used += 1
            phase = 2
        elif phase == 2:
            bit = stacks[1][0]
            if mutant != 'stale_response':
                stacks[1].pop(0)
            stacks[2].insert(0, bit)
            phase = 0
            charge += 4
        elif stacks[2]:
            bit = stacks[2].pop(0 if mutant != 'skip_reverse' else -1)
            stacks[3].insert(0, bit)
            charge += 5
        else:
            phase = None
            charge += 5  # syntactic branch cost uses the longest branch
    return phase, stacks, used, ticks, charge


def check(bits, width, modulus):
    got = execute(width, bits, modulus)
    n = len(bits)
    expected = (None, [[], [], [], bits, modulus], n, 4*n+2, 15*n+9)
    assert got == expected, (bits, width, modulus, got, expected)


assert execute([True, True], [False, True], [], 'skip_reverse')[1][3] != [False, True]
assert execute([], [], [], 'extra_coin') == 'excess query'
assert execute([True], [True], [], 'stale_response')[1][1] != []
exhaustive = 0
for n in range(10):
    for bits in itertools.product([False, True], repeat=n):
        check(list(bits), [True]*n, [False, True, False])
        exhaustive += 1
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(500):
        n = rng.randrange(257)
        check([bool(rng.getrandbits(1)) for _ in range(n)],
              [bool(rng.getrandbits(1)) for _ in range(n)],
              [bool(rng.getrandbits(1)) for _ in range(rng.randrange(129))])
print(json.dumps(dict(exhaustive=exhaustive, seeded=1500, seeds=[7,19,41],
    width=[0,256], modulus_width=[0,128], failures=0, gaveUp=0,
    detected_mutants=['skip_reverse','extra_coin','stale_response'],
    ticks='4*w+2', charge='15*w+9'), indent=2))
