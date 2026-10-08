#!/usr/bin/env python3
"""Finite dictionary oracle for ballot projection and retained proof domains."""
import itertools
import json

keys = [(tag, i) for tag in ('ballot', 'key', 'decryption') for i in range(2)]

def step(cache, key, coin):
    result = dict(cache)
    answer = result.setdefault(key, coin)
    return answer, result

def project(cache):
    return {k[1]: v for k, v in cache.items() if k[0] == 'ballot'}

def rebuild(cache, ballot):
    return ({k: v for k, v in cache.items() if k[0] != 'ballot'} |
            {('ballot', k): v for k, v in ballot.items()})

states = branches = 0
detected = set()
for values in itertools.product([None, 0, 1], repeat=len(keys)):
    cache = {k: v for k, v in zip(keys, values) if v is not None}
    states += 1
    assert rebuild(cache, project(cache)) == cache
    for i, coin in itertools.product(range(2), range(2)):
        key = ('ballot', i)
        answer, after = step(cache, key, coin)
        ballot_answer, ballot_after = step(project(cache), i, coin)
        expected = ballot_answer, rebuild(cache, ballot_after)
        assert (answer, after) == expected
        branches += 1
        mutants = {
            'reset_all': step({}, key, coin),
            'drop_other_domains': (ballot_answer, rebuild({}, ballot_after)),
            'erase_prior_ballots': step(rebuild(cache, {}), key, coin),
            'overwrite_hit': (coin, cache | {key: coin}),
        }
        for name, result in mutants.items():
            if result != expected:
                detected.add(name)

# Mixed pre-election and ballot requests retain earlier answers in every branch.
traces = 0
for requests in itertools.product(keys, repeat=3):
    for tape in itertools.product(range(2), repeat=3):
        cache = {}
        for key, coin in zip(requests, tape):
            before = dict(cache)
            answer, cache = step(cache, key, coin)
            assert all(cache[k] == v for k, v in before.items())
            if key[0] == 'ballot':
                a, b = step(project(before), key[1], coin)
                assert (answer, cache) == (a, rebuild(before, b))
        traces += 1
assert detected == {'reset_all', 'drop_other_domains', 'erase_prior_ballots', 'overwrite_hit'}
print(json.dumps(dict(states=states, ballot_response_branches=branches,
                      mixed_traces=traces, detected_mutants=sorted(detected),
                      failures=0, gaveUp=0), indent=2))
