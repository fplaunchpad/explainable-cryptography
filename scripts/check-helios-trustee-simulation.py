#!/usr/bin/env python3
"""Independent multiplicative trustee transcript and cached-step enumeration."""
from collections import Counter
from fractions import Fraction
import json

P, Q, SECRET = 23, 11, 3

def exp(xs, r):
    return tuple(pow(x, r, P) for x in xs)

def sim_commit(base, key, c, z):
    return tuple(pow(g, z, P) * pow(pow(k, c, P), -1, P) % P
                 for g, k in zip(base, key))

def tv(a, b):
    return sum(abs(a.get(x, 0)-b.get(x, 0)) for x in a.keys() | b.keys())/2

def add(dist, out, mass):
    dist[out] += mass

transcripts = cached_cases = 0
max_distance = Fraction(0)
for base in [(2,), (2, 3)]:
    key = exp(base, SECRET)
    def hash_key(commitment):
        return ('key', 2, key[0], commitment) if len(base) == 1 else (
            'decryption', 2, key[0], (3, 13), key[1], commitment)
    real, sim, nonzero = Counter(), Counter(), Counter()
    for r in range(Q):
        for c in range(Q):
            t = (exp(base, r), c, (r+c*SECRET) % Q)
            add(real, t, Fraction(1, Q*Q))
            if r:
                add(nonzero, t, Fraction(1, (Q-1)*Q))
            transcripts += 1
    for c in range(Q):
        for z in range(Q):
            commitment = sim_commit(base, key, c, z)
            assert exp(base, z) == tuple(a*b % P for a, b in zip(commitment, exp(key, c)))
            add(sim, (commitment, c, z), Fraction(1, Q*Q))
    assert real == sim
    assert tv(nonzero, sim) == Fraction(1, Q)  # Exact equality is false for historical coins.
    counts = Counter(t[0] for t in sim)
    assert max(counts.values()) == Q  # Point probability 1/Q.
    if len(base) == 2:
        assert len(counts) == Q < Q*Q  # Not surjective onto the product group.
    for cache_nonce in range(Q):
        for answer in range(Q):
            initial = {hash_key(exp(base, cache_nonce)): answer}
            actual, programmed = Counter(), Counter()
            for r in range(1, Q):
                commitment = exp(base, r)
                k = hash_key(commitment)
                for coin in range(Q):
                    cache = dict(initial)
                    c = cache.setdefault(k, coin)
                    out = ((commitment, (r+c*SECRET) % Q), False, frozenset(cache.items()))
                    add(actual, out, Fraction(1, (Q-1)*Q))
            for c in range(Q):
                for z in range(Q):
                    commitment = sim_commit(base, key, c, z)
                    k = hash_key(commitment)
                    cache = dict(initial)
                    bad = k in cache
                    cache.setdefault(k, c)
                    assert all(cache[k0] == c0 for k0, c0 in initial.items())
                    if not bad:
                        assert cache[k] == c
                    out = ((commitment, z), bad, frozenset(cache.items()))
                    add(programmed, out, Fraction(1, Q*Q))
            distance = tv(actual, programmed)
            assert distance <= Fraction(2, Q)
            max_distance = max(max_distance, distance)
            cached_cases += 1
# Literal old transcripts: nonce4, challenge5, response8; simulator reconstructs them.
assert sim_commit((2,), (8,), 5, 8) == (16,)
assert sim_commit((2, 3), (8, 4), 5, 8) == (16, 12)
assert sim_commit((2,), (8,), 6, 8) != (16,)
assert sim_commit((2, 3), (8, 4), 6, 8) != (16, 12)
assert transcripts == cached_cases == 242
print(json.dumps(dict(full_transcripts=transcripts, cached_cases=cached_cases,
                     historical_tv='1/11', maximum_cached_tv=str(max_distance),
                     rejected_claims=['exact_nonzero_simulation', 'product_surjectivity'],
                     changed_challenge_controls=2, failures=0, gaveUp=0), indent=2))
