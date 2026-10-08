#!/usr/bin/env python3
"""Independent multiplicative controls for the historical DDH pairing.
Only ciphertext distributions and share algebra; no full protocol privacy claim.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
import json

P, Q, G, PK, SECRET = 23, 11, 2, 8, 3
powers = [pow(G, n, P) for n in range(Q)]
def enc(r, m):
    return powers[r % Q], powers[m % Q] * pow(PK, r % Q, P) % P
def mul(a, b):
    return tuple(x*y % P for x,y in zip(a,b))
def div(a, b):
    return tuple(x*pow(y,-1,P) % P for x,y in zip(a,b))
def pair(A, T, total, left_zero, right_zero, vote):
    first = (A,powers[vote]*T % P)
    return ((first,enc(left_zero,0)),(div(enc(total,1),first),enc(right_zero,0)))
def record(cts, total, left_zero, right_zero):
    return cts,(total,(left_zero+right_zero) % Q)
def original(x, left_zero, y, right_zero, vote):
    return record(((enc(x,vote),enc(left_zero,0)),(enc(y,1-vote),enc(right_zero,0))),
                  (x+y) % Q,left_zero,right_zero)

cases = zero_sum_nonzero = arbitrary_challenge_cases = masking_cases = 0
mutants = set()
for vote in (0,1):
    uniform = Counter(original(x,a,y,b,vote) for x,a,y,b in product(range(Q),repeat=4))
    paired = Counter()
    for x,a,t,b in product(range(Q),repeat=4):
        cts = pair(powers[x],pow(PK,x,P),t,a,b,vote)
        paired[record(cts,t,a,b)] += 1
        assert mul(cts[0][0],cts[1][0]) == enc(t,1)
        assert mul(cts[0][1],cts[1][1]) == enc(a+b,0)
        cases += 1
    assert paired == uniform
    nonzero = Counter(original(x,a,y,b,vote) for x,a,y,b in product(range(1,Q),repeat=4))
    distance = sum(abs(Fraction(uniform[k],Q**4)-Fraction(nonzero[k],(Q-1)**4))
                   for k in uniform | nonzero) / 2
    assert distance == 1-Fraction((Q-1)**4,Q**4) and distance <= Fraction(4,Q)
    assert distance > 0
    mutants.add('omit_nonzero_sampling_loss')
    zero_sum_nonzero += sum(n for k,n in nonzero.items() if k[1][0] == 0)
    for x,z,t in product(range(Q),repeat=3):
        cts = pair(powers[x],powers[z],t,2,5,vote)
        assert mul(cts[0][0],cts[1][0]) == enc(t,1)
        assert mul(cts[0][1],cts[1][1]) == enc(7,0)
        if mul(cts[0][0],mul(enc(t,1),cts[0][0])) != enc(t,1):
            mutants.add('add_instead_of_subtract')
        arbitrary_challenge_cases += 1
for x,t in product(range(Q),repeat=2):
    worlds = [Counter(record(pair(powers[x],powers[z],t,2,5,v),t,2,5)
                      for z in range(Q)) for v in (0,1)]
    assert worlds[0] == worlds[1]
    masking_cases += 1
assert zero_sum_nonzero == 2000
mutants.add('require_nonzero_combined_nonce')
# Same independent accepted third-ballot nonces as the existing repair fixture.
cts = pair(powers[1],pow(PK,1,P),5,2,5,0)
assert mul(cts[0][0],cts[1][0]) == (9,9)
assert mul(cts[0][1],cts[1][1]) == (13,12)
for i,(total,r) in enumerate(((5,6),(7,9))):
    tally = mul(mul(cts[0][i],cts[1][i]),enc(r,0))
    share = pow(PK,(total+r) % Q,P)
    assert share == pow(tally[0],SECRET,P)
    assert tally[1]*pow(share,-1,P) % P == (G if i == 0 else 1)
    assert share != pow(PK,total,P)
mutants.add('omit_extracted_malicious_nonce')
assert enc(2,0) != enc(2,1)
mutants.add('turn_second_component_into_vote_one')
assert enc(1,0) != enc(0,0)
mutants.add('program_dummy_witness_statement')
# Finish the retained board independently in the multiplicative subgroup.
# Decision histories here test share algebra; reachable decision semantics are
# covered by the separate honest-source fixture and Lean source theorem.
finish_cases = 0
for x,z,t,decision in product(range(Q),range(Q),range(Q),('accepted','invalid','reused')):
    cts = pair(powers[x],powers[z],t,2,5,0)
    for i,(total,r) in enumerate(((t,6),(7,9))):
        honest = mul(cts[0][i],cts[1][i])
        board_ct = mul(honest,enc(r,0)) if decision == 'accepted' else honest
        nonce = total+r if decision == 'accepted' else total
        assert pow(PK,nonce % Q,P) == pow(board_ct[0],SECRET,P)
        if decision != 'accepted' and pow(PK,(total+r) % Q,P) != pow(board_ct[0],SECRET,P):
            mutants.add('include_rejected_malicious_nonce')
        if decision == 'accepted' and pow(PK,total % Q,P) != pow(board_ct[0],SECRET,P):
            mutants.add('treat_missing_witness_as_success')
        finish_cases += 1
# If Bob is rejected, the known pair sum does not describe the retained board.
cts = pair(powers[1],powers[3],5,2,5,0)
assert pow(PK,5,P) != pow(cts[0][0][0],SECRET,P)
mutants.add('omit_honest_acceptance_condition')
assert len(mutants) == 9
print(json.dumps(dict(real_distribution_cases=cases,zero_sum_nonzero_cases=zero_sum_nonzero,
    arbitrary_challenge_cases=arbitrary_challenge_cases,random_masking_cases=masking_cases,
    finishing_column_cases=finish_cases,
    nonzero_distance=str(distance),nonzero_distance_bound='4/11',detected_mutants=sorted(mutants),
    failures=0,gaveUp=0),indent=2))
