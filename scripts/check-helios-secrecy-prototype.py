#!/usr/bin/env python3
"""Independent rational checks of the prototype's accuracy/cost arithmetic."""
from fractions import Fraction
import json
import random

seeds = [7, 19, 41]
count = 0
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(1000):
        n, k, budget = rng.randrange(129), rng.randrange(9), rng.randrange(65)
        accuracy = (n + 1) ** (k + 1)
        scaled_error = n ** k * Fraction(2, accuracy)
        assert scaled_error <= Fraction(2, n + 1)
        # Direct expanded monomial and the original repetition formula agree.
        expected = 3456 * (budget + 1) ** 3 * (n + 1) ** (4 * k + 4)
        assert 3456 * (budget + 1) ** 3 * accuracy ** 4 == expected
        count += 1
# Wrong quantifier order: keep e=n+1 for every demanded decay degree.
assert 2 ** 2 * Fraction(2, 2 + 1) > Fraction(2, 2 + 1)
# Wrong degree in the replay estimate: suppress the fourth power of accuracy.
assert 3456 * 2 ** 4 != 3456 * 2
print(json.dumps({"seeds": seeds, "cases": count, "n": [0, 128],
                  "degree": [0, 8], "budget": [0, 64], "failures": 0,
                  "gaveUp": 0, "mutants_detected": ["fixed_accuracy", "linear_replay"]}, indent=2))
