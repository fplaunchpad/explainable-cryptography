#!/usr/bin/env python3
"""Independent finite residue and independent-pair fixtures; not a cost proof."""
from collections import Counter
import json

# Refutation gates: offset admits zero, omitted endpoint loses support,
# correlated draws have correct marginals but the wrong joint distribution.
q = 5
expected = Counter((a, b) for a in range(1, q) for b in range(1, q))
assert list(range(q - 1)) != list(range(1, q))
assert list(range(1, q - 1)) != list(range(1, q))
assert Counter((a, a) for a in range(1, q) for _ in range(q - 1)) != expected
# Modulo reduction of all q residues onto q-1 nonzero values is biased.
assert len(set(Counter(i % (q - 1) + 1 for i in range(q)).values())) > 1
primes = [3, 5, 7, 11, 17]
checks = pairs = 0
for q in primes:
    expected = list(range(1, q))
    actual = [i + 1 for i in range(q - 1)]
    assert actual == expected
    assert [a - 1 for a in actual] == list(range(q - 1))
    assert Counter((a, b) for a in actual for b in actual) == Counter(
        (a, b) for a in expected for b in expected)
    checks += q - 1
    pairs += (q - 1) ** 2
print(json.dumps(dict(primes=primes, residues=checks, independent_pairs=pairs,
    detected_mutations=['zero_offset', 'missing_endpoint', 'reused_nonce', 'modulo_bias'],
    failures=0, gaveUp=0), indent=2))
