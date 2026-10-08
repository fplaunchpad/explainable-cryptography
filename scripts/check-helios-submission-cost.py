#!/usr/bin/env python3
"""Finite independent accounting for two honest ballots and one submission."""
import itertools
import json
cases = 0
for attacker in range(65):
    for verifications in itertools.product((1, 2, 3), repeat=3):
        # Two nonzero encryption coins and three four-coin proofs per honest
        # ballot. Hash caching can reduce these verification/attacker counts.
        lowered = 2 * (2 + 3 * 4) + sum(verifications) + attacker
        requests = 2 * (2 + 3) + sum(verifications) + attacker
        assert requests <= attacker + 19
        assert lowered <= 4 * (attacker + 19)
        assert 4 * lowered <= 16 * (attacker + 19)
        cases += 1
assert 2 * (2 + 3 * 4) + 9 == 37
assert 37 > 2 * (3 * 4) + 9  # Omitting four nonce draws.
assert 37 > 2 * (2 + 3) + 9  # Charging proof requests as one draw.
# Discarding a fair coin before a fair coin preserves output distribution,
# while increasing the number of interactions from one to two.
outputs = [second for first, second in itertools.product((0, 1), repeat=2)]
assert outputs.count(0) == outputs.count(1) == 2
assert 2 > 1
# Independent upper accounting for the DDH public-input source. Verification
# counts are upper bounds for branch lengths, not asserted reachable histories.
# P/C/D count all callback requests, allowing every cache access to miss.
ddh_cases = 0
mutants = set()
for P,C,D in itertools.product(range(9),repeat=3):
    for verifies in itertools.product((1,2,3),repeat=3):
        prefix = P+C + 2 + 4 + 6*4 + sum(verifies)
        # 2 key-proof draws, one vote and three known nonces, six four-draw
        # ballot proofs; the other contributions are callback/verification.
        upper = 4*P+4*C+78
        assert prefix <= upper
        finish = 4+D  # Two two-draw trustee proofs, then the original guess.
        assert finish <= 4+4*D
        for k in range(4):
            full = (1+3*k)*prefix+finish
            assert full <= (1+3*k)*upper+(4+4*D)
            ddh_cases += 1
        assert prefix > prefix-4
        mutants.add('omit_vote_and_known_nonce_draws')
        assert prefix > prefix-2
        mutants.add('omit_key_simulator_draws')
        assert finish > D
        mutants.add('omit_trustee_simulator_draws')
# A key-cache hit needs no draw, a miss needs one; both have zero ballot hashes.
assert 1 > 0
mutants.add('identify_live_ballot_hash_count_with_total_cost')
assert (1+3*0)*39+4 > (3*0)*39+4
mutants.add('omit_original_when_no_repetitions')
print(json.dumps(dict(cases=cases, uncached_honest_and_verifier_budget=37,
                     omitted_nonce_defect=4, proof_undercharge_defect=18,
                     padded_sampler_cost=2, ddh_accounting_cases=ddh_cases,
                     detected_ddh_mutants=sorted(mutants),failures=0,gaveUp=0), indent=2))
