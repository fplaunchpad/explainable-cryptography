#!/usr/bin/env python3
"""Independent full/split oracle executions and replay event roles."""
import itertools
import json

keys = [(tag, i) for tag in ('ballot', 'key', 'decryption') for i in range(2)]
cases = 0
detected = set()
for requests in itertools.product(keys, repeat=4):
    for tape in itertools.product(range(2), repeat=4):
        full, ballot, auxiliary = {}, {}, {}
        direct_answers, split_answers, events, log = [], [], [], []
        for key, coin in zip(requests, tape):
            direct_answers.append(full.setdefault(key, coin))
            target = ballot if key[0] == 'ballot' else auxiliary
            if key not in target:
                target[key] = coin
                events.append(('challenge' if key[0] == 'ballot' else 'uniform', key))
                if key[0] == 'ballot':
                    log.append(key)
            split_answers.append(target[key])
        assert direct_answers == split_answers and full == ballot | auxiliary
        assert log == [key for role, key in events if role == 'challenge']
        if ballot != full:
            detected.add('erase_auxiliary_state')
        if [key for _, key in events] != log:
            detected.add('count_auxiliary_as_challenge')
        if len(log) > 1:
            assert log[1:] != log
            detected.add('erase_earlier_ballot_history')
        bad, bad_answers = {}, []
        for key, coin in zip(requests, tape):
            if key[0] != 'ballot':
                bad[key] = coin
            bad_answers.append(bad.setdefault(key, coin))
        if bad_answers != direct_answers:
            detected.add('resample_auxiliary_hit')
        cases += 1
assert detected == {'erase_auxiliary_state', 'count_auxiliary_as_challenge',
                    'erase_earlier_ballot_history', 'resample_auxiliary_hit'}
# Literal five-request history used by the Lean mixed-source control.
cache, answers = {}, []
for key, coin in zip([keys[0], keys[2], keys[4], keys[2], keys[0]], [3, 5, 7, 1, 2]):
    answers.append(cache.setdefault(key, coin))
assert answers == [3, 5, 7, 5, 3]
print(json.dumps(dict(traces=cases, directed_five_request_traces=1,
                      detected_mutants=sorted(detected),
                      failures=0, gaveUp=0), indent=2))
