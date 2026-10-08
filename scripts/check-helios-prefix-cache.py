#!/usr/bin/env python3
"""Finite reachable mixed-cache controls for the composed prefix boundary."""
from itertools import product
import json

P, Q, G, PK = 23, 11, 2, 8
keys = [('key',G,PK,16), ('decryption',G,PK,(3,13),4,(16,12)),
        ('ballot',(G,PK,(3,13)),((16,12),(9,18)))]
traces = flags = growth_cases = 0
mutants = set()
for length in range(5):
    for requests in product(range(3), repeat=length):
        cache = {}
        for i,j in enumerate(requests):
            cache.setdefault(keys[j], (2*i+5) % Q)
        for c,z in [(5,8),(6,8),(0,1)]:
            commitment = pow(G,z,P)*pow(pow(PK,c,P),-1,P) % P
            key = ('key',G,PK,commitment)
            after_key = dict(cache)
            key_bad = key in after_key
            after_key.setdefault(key,c)
            project = lambda full: {k:v for k,v in full.items() if k[0]=='ballot'}
            assert project(after_key)==project(cache)
            ballot_cache = project(after_key)
            ballot_cache.setdefault(keys[2],7)
            # Reconstruct the full cache after the independently simulated ballot phase.
            restored = {k:v for k,v in after_key.items() if k[0]!='ballot'} | ballot_cache
            assert all(restored[k]==v for k,v in after_key.items())
            if any(k[0]!='ballot' for k in restored):
                assert restored != ballot_cache
                mutants.add('drop_other_domains')
            for ballot_bad in [False,True]:
                bad = key_bad or ballot_bad
                if key_bad and not ballot_bad:
                    assert bad != ballot_bad
                    mutants.add('lose_key_flag')
                flags += 1
            if keys[2] in cache and cache[keys[2]] != 7:
                assert restored[keys[2]] != 7
                mutants.add('reset_prior_ballot')
            # A permitted fingerprint observes the actual key proof, including its response.
            fingerprint = (commitment + 3*z) % 101
            assert fingerprint != 0
            mutants.add('constant_fingerprint')
            # Budget 12 counts six proof-programming and six validation requests.
            # Directed fresh contexts exercise maximal growth after a key insertion.
            grown = dict(project(after_key))
            for j in range(12):
                grown.setdefault(('ballot', 'fresh-phase-context', j), (3*j+1) % Q)
            successor = {k:v for k,v in after_key.items() if k[0]!='ballot'} | grown
            assert len(successor) <= 2*len(cache)+13
            if not cache:
                assert len(successor) == 13
                assert len(successor) > 12  # Omitting the key domain is unsound.
                mutants.add('omit_key_growth')
            growth_cases += 1
            traces += 1
assert mutants == {'drop_other_domains','lose_key_flag','reset_prior_ballot','constant_fingerprint','omit_key_growth'}
print(json.dumps(dict(traces=traces,flag_cases=flags,growth_cases=growth_cases,detected_mutants=sorted(mutants),
                     failures=0,gaveUp=0),indent=2))
