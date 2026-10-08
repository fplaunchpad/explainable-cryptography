#!/usr/bin/env python3
"""Independent finite cache/miss-log comparison over reachable histories."""
import json
keys = [(s, c) for s in (0, 1) for c in (0, 1)]


def step(state, key, draw, mutant=None):
    entries, log = state
    if key is None:
        return draw, state, 1
    old = next((v for k, v in entries
                if (k[1] == key[1] if mutant == 'commit_only' else k == key)), None)
    if old is not None:
        return old, (entries, log + [key] if mutant == 'log_hit' else log), 0
    added = [key] + log if mutant == 'prepend' else log + [key]
    return draw, ([(key, draw)] + entries, added), 1


# Detect deliberate log mutations before checking the actual transition.
a = ((0, 0), 0)
b = ((1, 0), 1)
_, state, _ = step(([], []), *a)
assert step(state, *a, 'log_hit')[1][1] != [a[0]]
assert step(state, *b, 'prepend')[1][1] != [a[0], b[0]]
# Same commitment, different full statements must miss independently.
assert step(state, *b)[2] == 1
assert step(state, *b, 'commit_only')[2] == 0
assert dict(state[0]).get(b[0]) is None

frontier = [({}, [], [], [], 0)]
cases = hits = misses = uniforms = 0
for depth in range(4):
    following = []
    for cache, expected_log, entries, actual_log, fresh in frontier:
        for key in [None, *keys]:
            for draw in (0, 1):
                updated, log = dict(cache), list(expected_log)
                if key is None:
                    expected, draws = draw, 1
                    uniforms += 1
                elif key in cache:
                    expected, draws = cache[key], 0
                    hits += 1
                else:
                    expected, draws = draw, 1
                    updated[key] = draw
                    log.append(key)
                    misses += 1
                answer, state, used = step((entries, actual_log), key, draw)
                assert (answer, used) == (expected, draws)
                assert dict(state[0]) == updated and state[1] == log
                assert len(state[0]) == len(state[1]) == len(set(state[1]))
                cases += 1
                following.append((updated, log, state[0], state[1], fresh + draws))
    frontier = following
print(json.dumps(dict(cases=cases, hits=hits, misses=misses, uniforms=uniforms,
                      mutation_controls=3, failures=0, gaveUp=0), indent=2))
