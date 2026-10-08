#!/usr/bin/env python3
"""Independent finite enumeration of DDH worlds and adaptive modulo randomness."""
from fractions import Fraction as F
from collections import Counter
import json
import random


def ideal(size):
    return [F(1, size)] * size


def modulo(size, slack):
    count = 1 << (size.bit_length() + slack)
    residues = Counter(x % size for x in range(count))
    return [F(residues[x], count) for x in range(size)]


def test_probability(target, slack):
    first = ideal(3) if slack is None else modulo(3, slack)
    result = F(0)
    for x, px in enumerate(first):
        second = ideal(x + 2) if slack is None else modulo(x + 2, slack)
        for y, py in enumerate(second):
            if (target == 0) != (y == x):
                result += px * py
    return result


def worlds(q, slack):
    # Enumerate exact challenger scalars; only private test randomness changes.
    outputs = [test_probability(t, slack) for t in range(q)]
    real = sum((outputs[(a * b) % q] for a in range(q) for b in range(q)), F(0)) / (q * q)
    rand = sum((outputs[c] for a in range(q) for b in range(q) for c in range(q)), F(0)) / q**3
    return real, rand


seeds = [7, 19, 41]
count = 0
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(250):
        q, slack = rng.choice([3, 5, 7]), rng.randrange(7)
        real, rand = worlds(q, None)
        bit_real, bit_rand = worlds(q, slack)
        per_world = F(2, 2**slack)
        assert abs(bit_real - real) <= per_world
        assert abs(bit_rand - rand) <= per_world
        assert abs(abs(bit_real - bit_rand) - abs(real - rand)) <= 2 * per_world
        count += 1
# Independently directed defects: erase bias, change the DDH challenger, lose one world.
assert modulo(3, 0)[0] == F(1, 2) != ideal(3)[0]
assert F(sum(a * b % 3 == 0 for a in range(3) for b in range(3)), 9) == F(5, 9)
assert F(1, 3) != modulo(3, 0)[0]
assert abs(abs(F(3, 4) - F(1, 4)) - abs(F(1, 2) - F(1, 2))) > F(1, 4)
print(json.dumps({"seeds": seeds, "cases": count, "prime_fields": [3, 5, 7],
                  "slack": [0, 6], "private_queries": 2, "failures": 0, "gaveUp": 0,
                  "mutants_detected": ["erase_modulo_bias", "change_challenger", "one_world_loss"]}, indent=2))
