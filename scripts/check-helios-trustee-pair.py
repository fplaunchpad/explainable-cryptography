#!/usr/bin/env python3
"""Independent multiplicative two-proof/cache/continuation distribution check."""
from collections import Counter
from fractions import Fraction
from itertools import product
import json

P, Q, G, SECRET = 23, 11, 2, 3
PK = pow(G, SECRET, P)

def tag(ct, share, commitment):
    return ('decryption', G, PK, ct, share, commitment)

def step(ct, initial, first, second, simulated):
    share = pow(ct[0], SECRET, P)
    cache = dict(initial)
    if simulated:
        c, z = first, second
        commitment = (pow(G, z, P)*pow(pow(PK, c, P), -1, P) % P,
                      pow(ct[0], z, P)*pow(pow(share, c, P), -1, P) % P)
        k = tag(ct, share, commitment)
        bad = k in cache
        cache.setdefault(k, c)
    else:
        r, coin = first, second
        commitment = (pow(G, r, P), pow(ct[0], r, P))
        k = tag(ct, share, commitment)
        c = cache.setdefault(k, coin)
        z, bad = (r + c*SECRET) % Q, False
    assert all(cache[k0] == a for k0, a in initial.items())
    return (commitment, z), bad, cache, k

def distribution(cts, initial, simulated):
    out = Counter()
    coins = list(product(range(Q) if simulated else range(1, Q), range(Q)))
    for a, b in coins:
        p0, bad0, cache0, k0 = step(cts[0], initial, a, b, simulated)
        for c, d in coins:
            p1, bad1, cache1, k1 = step(cts[1], cache0, c, d, simulated)
            # An adaptive continuation repeats a proof-dependent actual query.
            reply = cache1[k0 if p1[1] % 2 else k1]
            out[(p0, p1, bad0 or bad1, reply, frozenset(cache1.items()))] += 1
    total = len(coins)**2
    return {x: Fraction(n, total) for x, n in out.items()}

def tv(a, b):
    return sum(abs(a.get(x, 0)-b.get(x, 0)) for x in a.keys() | b.keys()) / 2

cases = 0
maximum = Fraction(0)
for cts in [((3,13),(3,13)), ((3,13),(4,9))]:
    k = tag(cts[0], pow(cts[0][0], SECRET, P), (pow(G,4,P),pow(cts[0][0],4,P)))
    for initial in [{}, {k: 5}, {k: 7}]:
        real = distribution(cts, initial, False)
        sim = distribution(cts, initial, True)
        distance = tv(real, sim)
        assert distance <= Fraction(2*len(initial)+3, Q)
        maximum = max(maximum, distance)
        cases += 1
# A first-step hit followed by a fresh second proof must remain flagged.
ct0, ct1 = (3,13), (4,9)
k = tag(ct0, pow(ct0[0],SECRET,P), (16,12))
p0,b0,cache0,_ = step(ct0,{k:5},5,8,True)
p1,b1,cache1,_ = step(ct1,cache0,0,1,True)
assert b0 and not b1 and (b0 or b1) != b1
assert cache1[k] == 5  # Overwriting with a different simulated challenge is invalid.
_,_,hit_cache,_ = step(ct0,{k:7},5,8,True)
assert hit_cache[k] == 7 and hit_cache[k] != 5
print(json.dumps(dict(cases=cases, maximum_tv=str(maximum),
                     sticky_flag_mutant_detected=True, overwrite_mutant_detected=True,
                     failures=0, gaveUp=0), indent=2))
