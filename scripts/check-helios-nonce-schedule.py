#!/usr/bin/env python3
"""Finite independent oracle for moving private trustee coins to use points."""
from collections import Counter
from itertools import product
import json

Q = 3
NONZERO = (1, 2)

def ask(cache, key, coin):
    return cache.setdefault(key, coin)

def execute(key_nonce, r0, r1, honest_coin, answers, initial, reset=False):
    cache = dict(initial)
    key_c = ask(cache, ('key', 1, 2, key_nonce), answers[0])
    key_proof = (key_nonce, (key_nonce + 2*key_c) % Q)
    # Earlier adaptive ballot and submission queries choose the published tally.
    b = ask(cache, ('ballot', honest_coin, key_proof), answers[1])
    c = ask(cache, ('submit', b), answers[2])
    accepted = c != 0
    tally = (b + c) % Q if accepted else b
    if reset:
        cache = {}  # Invalid transformation: old answers are public commitments.
    proofs = []
    for r, coin in zip((r0, r1), answers[3:5]):
        commitment = (r, r*tally % Q)
        tag = ('decryption', 1, 2, (tally, b), 2*tally % Q, commitment)
        challenge = ask(cache, tag, coin)
        proofs.append((commitment, (r+2*challenge) % Q))
    view = (key_proof, honest_coin, b, accepted, tally, tuple(proofs))
    guess = ask(cache, ('guess', view), answers[5])
    return view, guess, frozenset(cache.items())

cases = 0
controls = 0
for initial in ({}, {('key', 1, 2, 1): 2, ('submit', 0): 1}):
    early, late, shared, reset = (Counter() for _ in range(4))
    # Enumeration order reflects the sampler schedules; each uses the same product law.
    for k, r0, r1, h in product(NONZERO, NONZERO, NONZERO, range(Q)):
        for answers in product(range(Q), repeat=6):
            early[execute(k, r0, r1, h, answers, initial)] += 1
            shared[execute(k, r0, r0, h, answers, initial)] += 1
            reset[execute(k, r0, r1, h, answers, initial, reset=True)] += 1
            cases += 1
    for h, k, r0, r1 in product(range(Q), NONZERO, NONZERO, NONZERO):
        for answers in product(range(Q), repeat=6):
            late[execute(k, r0, r1, h, answers, initial)] += 1
    assert early == late
    assert early != shared  # Two independent commitments cannot be replaced by one nonce.
    assert early != reset
    assert any(out[0][3] for out in early) and any(not out[0][3] for out in early)
    assert any(out[0][5][0] != out[0][5][1] for out in early)
    controls += 2
print(json.dumps(dict(cases=cases, initial_caches=2, detected_mutants=controls,
                     acceptance_and_rejection=True, failures=0, gaveUp=0), indent=2))
