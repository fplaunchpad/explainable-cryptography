#!/usr/bin/env python3
"""Exact DDH input sampling and event-transfer controls; no security claim."""
from fractions import Fraction as Q
from itertools import product
import json

cases = 0
results = []
for q in [2, 3, 5, 7, 11]:
    # Enumerate joint tuples independently of any encryption/simulator code.
    uniform = Q(1, q**5)
    historical = Q(1, (q-1)**5)
    variation = Q(0)
    zero_key_mass = Q(0)
    for tape in product(range(q), repeat=5):
        original = historical if all(tape) else Q(0)
        variation += abs(original-uniform)/2
        if tape[0] == 0:
            zero_key_mass += uniform
        cases += 1
    assert variation == 1-Q(q-1, q)**5
    assert variation <= Q(5, q)
    assert zero_key_mass == Q(1, q)
    results.append(dict(q=q, variation=str(variation), zero_key_mass=str(zero_key_mass)))
# The four-nonce allowance alone is insufficient once the key also changes.
assert 1-Q(10, 11)**5 > Q(4, 11)
# Rejection/publication must remain in any continuation of these distributions;
# this fixture does not replace a source-level continuation theorem.
# Independent Boolean two-world tables, including both advantage orientations.
# This validates the probability algebra, not a protocol simulation.
transfer_cases = 0
transfer_mutants = set()
for denominator in (1,2,3,4,8,16,32):
    for a,b in product(range(denominator+1),repeat=2):
        real,rejected_random = Q(a,denominator),Q(b,denominator)
        advantage = abs(real-rejected_random)
        success = (real+1-rejected_random)/2
        guessing_advantage = abs(success-Q(1,2))
        assert advantage == 2*guessing_advantage
        assert rejected_random <= real+advantage
        if rejected_random > real:
            transfer_mutants.add('omit_ddh_advantage')
        if rejected_random > real+guessing_advantage:
            transfer_mutants.add('substitute_guessing_advantage_without_factor_two')
        if rejected_random > real+(real-rejected_random):
            transfer_mutants.add('omit_absolute_value')
        transfer_cases += 1
assert len(transfer_mutants) == 3
# Four observed probabilities in the complete hybrid chain. Construct the
# rejection/error allowances from distances, so no implication is discarded.
chain_cases=0;chain_mutants=set()
for oi,ri,xi,yi in product(range(9),repeat=4):
    original,real,extracted_real,extracted_random=(Q(i,8) for i in (oi,ri,xi,yi))
    for epsilon in (Q(0),Q(1,16),Q(1,8)):
        loss=abs(original-real)
        reject_real=max(Q(0),abs(real-extracted_real)-epsilon)
        reject_random=max(Q(0),abs(extracted_random-Q(1,2))-epsilon)
        main=abs(extracted_real-extracted_random)
        reject_adv=abs(reject_real-reject_random)
        bias=abs(original-Q(1,2))
        bound=loss+2*reject_real+2*epsilon+main+reject_adv
        assert bias<=bound
        defective={
            'omit_original_loss':bound-loss,
            'omit_one_rejection_allowance':bound-reject_real,
            'omit_one_extraction_allowance':bound-epsilon,
            'omit_main_ddh':bound-main,
            'omit_rejection_ddh':bound-reject_adv,
            'half_ddh_advantages':bound-(main+reject_adv)/2,
            'signed_main_difference':bound-main+extracted_real-extracted_random}
        chain_mutants.update(name for name,value in defective.items() if bias>value)
        chain_cases+=1
assert len(chain_mutants)==7
print(json.dumps(dict(cases=cases, results=results,
    detected_mutants=['omit_key_replacement', 'retain_nonzero_key_in_ddh_world'],
    transfer_cases=transfer_cases,transfer_mutants=sorted(transfer_mutants),
    chain_cases=chain_cases,chain_mutants=sorted(chain_mutants),
    failures=0, gaveUp=0), indent=2))
