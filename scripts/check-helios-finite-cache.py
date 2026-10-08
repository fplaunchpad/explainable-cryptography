#!/usr/bin/env python3
"""Independent dictionary/list oracle comparison on reachable cache histories."""
import json
keys = [(stmt, commit) for stmt in (0, 1) for commit in (0, 1)]
cases = hits = misses = 0
frontier = [({}, [], 0)]
for depth in range(5):
    nxt = []
    for reference, entries, used in frontier:
        for key in keys:
            choices = [reference[key]] if key in reference else [0, 1]
            for draw in choices:
                expected = reference.get(key, draw)
                updated = dict(reference)
                updated.setdefault(key, draw)
                found = next((v for k, v in entries if k == key), None)
                answer = draw if found is None else found
                stored = [(key, draw)] + entries if found is None else entries
                assert answer == expected
                assert dict(stored) == updated
                assert len(stored) <= used + 1
                assert len(stored) == len({k for k, _ in stored})
                hits += found is not None
                misses += found is None
                cases += 1
                nxt.append((updated, stored, used + 1))
    frontier = nxt
# Directed mutations are detected by preserving answers and full key identity.
assert dict([((0, 0), 1)]) != {(0, 0): 0}  # Overwrite a cached answer.
assert {(1, 0): 1} != {(0, 0): 0, (1, 0): 1}  # Drop prior state.
assert {(0, 0): 0, (1, 0): 1}[(1, 0)] != {0: 0}[0]  # Drop statement from key.
print(json.dumps(dict(cases=cases, hit_cases=hits, miss_cases=misses,
                     mutation_controls=3, failures=0, gaveUp=0), indent=2))
