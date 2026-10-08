#!/usr/bin/env python3
"""Independent finite comparator traces versus equality and common-prefix cost."""
import itertools
import json


def machine(left, right, prefix_mutant=False):
    a, b = list(left), list(right)
    steps = 0
    while True:
        x = a.pop(0) if a else None
        y = b.pop(0) if b else None
        steps += 1
        if x is not None and x == y:
            continue
        return (x == y or (prefix_mutant and (x is None or y is None))), steps


words = [w for n in range(7) for w in itertools.product((False, True), repeat=n)]
assert machine((), (False,), True)[0]  # Known-broken acceptance detected first.
assert () != (False,)
cases = 0
for left in words:
    for right in words:
        result, steps = machine(left, right)
        common = next((i for i, (x, y) in enumerate(zip(left, right)) if x != y),
                      min(len(left), len(right)))
        assert result == (left == right)
        assert steps == common + 1
        assert steps <= min(len(left), len(right)) + 1
        cases += 1
print(json.dumps({'word_pairs': cases, 'maximum_word_length': 6,
                  'mutants_detected': ['strict_prefix_accepted'],
                  'failures': 0, 'gaveUp': 0}, indent=2))
