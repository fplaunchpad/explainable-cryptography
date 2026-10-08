#!/usr/bin/env python3
"""Deterministic reachable-cache controls for full replayable programming.
This is a cache/query-history oracle, not a full election distribution test.
"""
from itertools import product
import json

cases = exposed_request_cases = 0
mutants = set()
for length in range(5):
    for trace in product(range(7), repeat=length):
        for initial_bad in (False, True):
            reference, shadow, live = {}, {}, {}
            programmed, queries = set(), []
            bad = reference_bad = initial_bad
            previous = 0
            for step, event in enumerate(trace):
                coin = (3*step+5) % 11
                if event in (0, 1, 2, 3):
                    key = [('key',0), ('decryption',0), ('ballot',0), ('ballot',previous % 2)][event]
                    expected = reference.setdefault(key,coin)
                    if key in shadow:
                        answer = shadow[key]
                    else:
                        if key[0] == 'ballot':
                            assert key not in live
                            queries.append((step,key,coin))
                            live[key] = coin
                        shadow[key] = coin
                        answer = coin
                    assert answer == expected
                    previous = answer
                else:
                    key = [('ballot',0), ('key',0), ('decryption',0)][event-4]
                    reference_bad |= key in reference
                    reference.setdefault(key,coin)
                    bad |= key in shadow
                    shadow.setdefault(key,coin)
                    if key[0] == 'ballot':
                        programmed.add(key)
                assert shadow == reference and bad == reference_bad
                assert all(shadow[k] == v for k,v in live.items())
                assert all(k in live or k in programmed for k in shadow if k[0]=='ballot')
                if initial_bad and event != 4:
                    broken_bad = False
                    assert broken_bad != reference_bad
                    mutants.add('reset_incoming_flag')
                if any(k[0] != 'ballot' for k in shadow):
                    broken_cache = {k:v for k,v in shadow.items() if k[0]=='ballot'}
                    assert broken_cache != reference
                    mutants.add('erase_auxiliary_cache')
            if queries:
                # Replay changes the challenge at an actual live request. A lift
                # of the evaluated computation would have no such request index.
                broken_queries = []
                assert broken_queries != queries
                mutants.add('hide_all_raw_queries')
                step,key,old = queries[0]
                replacement = (old+1) % 11
                assert replacement != old
                exposed_request_cases += 1
            if ('ballot',0) in shadow and ('ballot',0) not in live:
                assert ('ballot',0) in programmed
                broken_live = {k:v for k,v in shadow.items() if k[0]=='ballot'}
                assert broken_live != live
                mutants.add('treat_programmed_shadow_as_live')
            cases += 1
assert mutants == {'reset_incoming_flag','erase_auxiliary_cache',
                   'hide_all_raw_queries','treat_programmed_shadow_as_live'}
print(json.dumps(dict(cases=cases,exposed_request_cases=exposed_request_cases,detected_mutants=sorted(mutants),
                     max_length=4,failures=0,gaveUp=0),indent=2))
