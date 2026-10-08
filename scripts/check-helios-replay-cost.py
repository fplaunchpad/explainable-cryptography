#!/usr/bin/env python3
"""Independent finite checks of original-plus-three residual interaction cost."""
import itertools
import json

# Leaves are represented by root-to-leaf answer tuples. Prefix closure and the
# first-zero stopping rule generate reachable variable-length ternary trees.
cases = 0
exact = 0
for depth in range(1, 6):
    paths = []
    for length in range(1, depth + 1):
        for prefix in itertools.product((1, 2), repeat=length - 1):
            paths.append(prefix + (0,))
        if length == depth:
            paths.extend(itertools.product((1, 2), repeat=length))
    for original in paths:
        for sites in itertools.product(range(len(original)), repeat=3):
            # Maximum length of an admissible second completion at each saved
            # site, derived by enumerating original-tree paths sharing its prefix.
            suffixes = [max(len(p) - site for p in paths
                            if p[:site] == original[:site]) for site in sites]
            cost = len(original) + sum(suffixes)
            assert cost <= 4 * depth
            cases += 1
            exact += cost == 4 * depth

# One query originally plus three one-query replays needs four interactions.
# A 3m bound which forgets the original execution is false at m=1.
assert 1 + 1 + 1 + 1 > 3 * 1
# A uniform-only source has zero hash cost but still consumes an interaction.
assert 1 > 4 * 0
print(json.dumps(dict(branch_cost_cases=cases, exact_bound_cases=exact,
                     omitted_original_counterexample=4,
                     ignored_uniform_counterexample=1,
                     failures=0, gaveUp=0), indent=2))
