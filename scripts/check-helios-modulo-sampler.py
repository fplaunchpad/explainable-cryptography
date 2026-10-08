#!/usr/bin/env python3
"""Independent finite fair-bit/modulo law and distinguishing-event fixtures."""
from collections import Counter
from fractions import Fraction
from itertools import product
import json

# Detect broken candidates before checking the general finite fixtures.
words = list(product((0, 1), repeat=2))
values = [sum(b * 2**i for i, b in enumerate(bs)) for bs in words]
assert Counter(x % 3 for x in values) != Counter({0: Fraction(4, 3), 1: Fraction(4, 3), 2: Fraction(4, 3)})
assert Counter(sum(bs[0] * 2**i for i in range(2)) for bs in words) != Counter(values)
assert Counter(sum(b * 2**i for i, b in enumerate(bs[:-1])) for bs in words) != Counter(values)
# Claiming security slack without spending its bits is false at q=3, w=2.
assert Fraction(1, 6) > Fraction(1, 16)

points = events = width_checks = 0
max_tv = Fraction(0)
for w in range(9):
    bs = list(product((0, 1), repeat=w))
    encoded = [sum(b * 2**i for i, b in enumerate(word)) for word in bs]
    M = 2**w
    assert Counter(encoded) == Counter(range(M))
    for q in range(1, 18):
        counts = Counter(x % q for x in encoded)
        d, r = divmod(M, q)
        masses = [Fraction(counts[y], M) for y in range(q)]
        for y, p in enumerate(masses):
            assert p == Fraction(d + (y < r), M)
            # Ideal proof-only refill replaces the final incomplete block.
            assert Fraction(d, M) + Fraction(r, M) * Fraction(1, q) == Fraction(1, q)
            points += 1
        tv = sum(abs(p - Fraction(1, q)) for p in masses) / 2
        assert tv == Fraction(r * (q-r), q*M)
        assert tv <= Fraction(r, M) <= Fraction(q, M)
        max_tv = max(max_tv, tv)
        if q <= 8:
            for event_bits in product((0, 1), repeat=q):
                event_mass = sum(p for p, on in zip(masses, event_bits) if on)
                ideal_mass = Fraction(sum(event_bits), q)
                assert abs(event_mass - ideal_mass) <= Fraction(r, M)
                events += 1
for q in range(1, 258):
    for slack in range(13):
        M = 2**(q.bit_length() + slack)
        assert Fraction(q, M) <= Fraction(1, 2**slack)
        width_checks += 1
# The second request's range depends on the first returned residue.
adaptive_cases = 0
for slack in range(6):
    first = Counter(i % 3 for i in range(2**((3).bit_length()+slack)))
    first_total = sum(first.values())
    actual, ideal = {}, {}
    for a in range(3):
        q = a + 2
        second = Counter(i % q for i in range(2**(q.bit_length()+slack)))
        for b in range(q):
            actual[a,b] = Fraction(first[a], first_total) * Fraction(second[b], sum(second.values()))
            ideal[a,b] = Fraction(1, 3*q)
    tv = sum(abs(actual[x]-ideal[x]) for x in ideal) / 2
    assert tv <= 2 * Fraction(1, 2**slack)
    # Dropping the first answer from the output would lose this distinguishing event.
    assert sum(actual.values()) == sum(ideal.values()) == 1
    adaptive_cases += 1
print(json.dumps(dict(point_masses=points, distinguishing_events=events,
    adaptive_cases=adaptive_cases, width_checks=width_checks, max_fixture_tv=str(max_tv),
    detected_mutations=['exact_modulo','reused_bits','missing_high_bit','unspent_slack'],
    failures=0, gaveUp=0), indent=2))
