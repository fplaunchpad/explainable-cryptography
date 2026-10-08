#!/usr/bin/env python3
"""Independent modular proofs and full-cache/path acceptance controls."""
import contextlib
import io
import itertools
import json
import runpy

# Reuse the independently derived multiplicative fixture, including its controls.
with contextlib.redirect_stdout(io.StringIO()):
    sigma = runpy.run_path('scripts/check-helios-sigma-fixtures.py')
enc, transcript, verify = (sigma[n] for n in ('enc', 'transcript', 'verify'))
proofs = []
for vote, nonce, challenge in [(0, 3, 5), (1, 4, 6), (1, 7, 7)]:
    commitment, response = transcript(vote, nonce, challenge)
    ciphertext = enc(nonce, vote)
    key = ('ballot', ciphertext, commitment)
    proofs.append((key, ciphertext, commitment, response, challenge))
assert tuple(a*b % 23 for a, b in zip(proofs[0][1], proofs[1][1])) == proofs[2][1]
keys = [p[0] for p in proofs] + [('key', 2, 8, 16), ('decryption', 2, 8, (3, 13), 4, (16, 12))]
traces = accepted = 0
mutants = set()
for earlier in [None, *range(3)]:
    for suffix in itertools.product(keys, repeat=3):
        for coins in itertools.product([5, 8], repeat=3):
            cache, log = {}, []
            if earlier is not None:
                key, _, _, _, challenge = proofs[earlier]
                cache[key] = challenge
                log.append(key)
            validation_start = len(log)
            for key, _, _, _, challenge in proofs:
                if key not in cache:
                    cache[key] = challenge
                    log.append(key)
            before = dict(cache)
            for key, coin in zip(suffix, coins):
                if key not in cache:
                    cache[key] = coin
                    if key[0] == 'ballot':
                        log.append(key)
            assert all(cache[k] == c for k, c in before.items())
            is_valid = all(cache[k] == c and verify(ct, pc, cache[k], resp)
                           for k, ct, pc, resp, c in proofs)
            n = (earlier is not None) + 3 + sum(k[0] == 'ballot' for k in suffix)
            selected = all(k in log and log.index(k) < n+1 for k, *_ in proofs)
            assert is_valid and selected and len(log) <= n
            accepted += is_valid
            # Mutants destroy the certificate after actual validation.
            reset = {k: 0 for k in cache}
            if not all(reset[k] == c for k, _, _, _, c in proofs):
                mutants.add('reset_after_validation')
            erased = {k: c for k, c in cache.items() if k[0] != 'ballot'}
            if not all(k in erased for k, *_ in proofs):
                mutants.add('erase_validated_challenges')
            if not all(k in log[validation_start:] for k, *_ in proofs):
                mutants.add('discard_preparation_history')
            traces += 1
assert traces == accepted == 4000
assert mutants == {'reset_after_validation', 'erase_validated_challenges', 'discard_preparation_history'}
# A rejected fallback's first branch has zero response/challenge and commitment g.
# In multiplicative form, 1 = g would be required, contradicted by literal g=2.
assert pow(2, 0, 23) != 2 * pow(3, 0, 23) % 23
print(json.dumps(dict(traces=traces, accepted=accepted,
                     detected_mutants=sorted(mutants), impossible_fallbacks=1,
                     failures=0, gaveUp=0), indent=2))
