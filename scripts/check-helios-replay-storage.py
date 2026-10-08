#!/usr/bin/env python3
"""Independent replay storage balance and fixed full-key layout fixtures."""
import itertools
import json

keys = [(s, c) for s in range(2) for c in range(2)]
starts = [({}, []), ({keys[0]: 0}, []),
          ({keys[0]: 0}, [keys[1], keys[1]]),
          ({keys[0]: 0, keys[1]: 1}, [keys[0]])]
# An unconditional cache/log equality is false before any action.
assert len(starts[1][0]) != len(starts[1][1])
# Run concrete broken transitions against the same balance predicate first.
def balance(initial, final):
    return len(final[0]) + len(initial[1]) == len(initial[0]) + len(final[1])

initial = ({keys[0]: 0}, [])
duplicate_hit = (dict(initial[0]), [keys[0]])
dropped_prior = ({keys[1]: 1}, [keys[1]])
assert not balance(initial, duplicate_hit)
assert not balance(initial, dropped_prior)
cases = 0
for cache0, log0 in starts:
    frontier = [(cache0, log0)]
    for depth in range(4):
        following = []
        for cache, log in frontier:
            for key, answer in itertools.product(keys, range(2)):
                updated, recorded = dict(cache), list(log)
                if key not in cache:
                    updated[key] = answer
                    recorded.append(key)
                assert balance((cache0, log0), (updated, recorded))
                assert len(updated) <= len(cache0) + depth + 1
                following.append((updated, recorded))
                cases += 1
        frontier = following
# Independent intended order: generator, public key, two ciphertext components,
# zero-branch commitment pair, one-branch commitment pair.
key = dict(generator=1, public_key=2, ciphertext=(3, 4), zero=(5, 6), one=(7, 8))
expected = list(range(1, 9))
actual = [key['generator'], key['public_key'], *key['ciphertext'], *key['zero'], *key['one']]
assert actual == expected
assert [2, 1, *actual[2:]] != expected
assert actual[1:] != expected
print(json.dumps(dict(storage_transitions=cases, initial_states=len(starts),
                      negative_controls=['preloaded_equal_counts', 'duplicate_hit',
                                         'drop_prior_entry', 'swapped_fields', 'dropped_generator'],
                      failures=0, gaveUp=0), indent=2))
