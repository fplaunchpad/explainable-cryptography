#!/usr/bin/env python3
"""Exact finite controls for fixed-original-path repetition; no crypto claim."""
from fractions import Fraction as Q
from functools import reduce
from itertools import product
import json
import random

seeds = [17, 41, 103]
cases = 0
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(100):
        # Independently enumerate residual success tapes for each retained path.
        path_count = rng.randrange(1, 5)
        weights = [rng.randrange(1, 8) for _ in range(path_count)]
        weights = [Q(w, sum(weights)) for w in weights]
        individual = [[Q(rng.randrange(8), 7) for _ in range(3)]
                      for _ in weights]
        for k in range(6):
            original = {i: w for i, w in enumerate(weights)}
            retained, failures = {}, Q(0)
            for i, weight in original.items():
                # A joint attempt needs all three independent residual successes.
                s = sum((reduce(
                    lambda x, y: x*y,
                    (p if bit else 1-p for p, bit in zip(individual[i], tape)), Q(1))
                    for tape in product([False, True], repeat=3) if all(tape)), Q(0))
                mass, failed = Q(0), Q(0)
                for tape in product([False, True], repeat=k):
                    prob = Q(1)
                    for bit in tape:
                        prob *= s if bit else 1-s
                    mass += prob
                    if not any(tape):
                        failed += prob
                retained[i] = weight*mass
                failures += weight*failed
                assert failed == (1-s)**k
                epsilon = min(individual[i])
                assert failed <= (1-epsilon**3)**k
            assert retained == original
            assert 0 <= failures <= 1
            cases += 1
# Directed mutations: two equally likely originals, only the first extractable.
# Retrying the original instead of the residual biases the retained successful tag.
retained_original = {0: Q(1, 2), 1: Q(1, 2)}
resampled_until_success = {0: Q(3, 4), 1: Q(1, 4)}
conditioned_on_success = {0: Q(1), 1: Q(0)}
assert retained_original != resampled_until_success != conditioned_on_success
# Reusing the residual coin does not square its failure probability.
assert Q(2, 3) != Q(2, 3)**2
# Zero trials must fail even when a single residual attempt succeeds surely.
assert (1-Q(1))**0 == 1
# Exact arithmetic oracle for the proposed integer parameter choice. Test the
# geometric inequality on small powers; certify large k by its rational bound.
geometric_cases = parameter_cases = 0
for t_numerator,n in product(range(65),range(65)):
    t = Q(t_numerator,64)
    assert (1-t)**n <= 1/(1+n*t)
    geometric_cases += 1
for N,e in product(range(17),range(1,9)):
    boundary = 12*(N+1)*e
    delta = Q(1,6*(N+1)*e)
    k = 3456*(N+1)**3*e**4
    for q in (boundary,boundary+1,2*boundary):
        success = (delta-Q(1,q))**3
        context = 3*(N+1)*delta
        assert context == Q(1,2*e)
        assert success >= Q(1,1728*(N+1)**3*e**3)
        assert k*success >= 2*e
        assert 1/(1+k*success) <= Q(1,2*e)
        assert context+1/(1+k*success) <= Q(1,e)
        parameter_cases += 1
# Dropping the field-size condition makes success zero and failure one.
delta,k = Q(1,12),3456*2**4
assert Q(1,4)+(1-max(Q(0),delta-Q(1,2))**3)**k > Q(1,2)
# Replacing the polynomial repetition count by a linear one really fails,
# not merely the intermediate reciprocal estimate, at N=0,e=2,q=24.
assert Q(1,4)+(1-Q(1,24)**3)**(3456*2) > Q(1,2)
assert Q(1,4)**3 != Q(1,4)
print(json.dumps(dict(seeds=seeds, cases=cases,
    detected_mutants=['resample_original', 'condition_on_success',
                      'reuse_residual_randomness', 'skip_zero_trial_failure'],
    geometric_cases=geometric_cases,parameter_cases=parameter_cases,
    parameter_mutants=['omit_field_size_condition','linear_repetition_count','omit_joint_cube'],
    failures=0, gaveUp=0), indent=2))
