#!/usr/bin/env python3
"""Small stateful sampler-substitution fixtures, independently enumerated."""
from collections import Counter
from itertools import product
import json

# Literal state transition exposes prior state and every rejected submission.
def observe(rs, initial):
    a, b, c, d = rs
    first = a != b
    second = c != d and c != a
    prefix = tuple(v for v, ok in [(0, first), (1, second)] if ok)
    # Adaptive choice depends on both decisions and the actual retained prefix.
    submit = (a + d + len(prefix)) % 3
    decision = submit != 0 and second
    final = prefix + ((2,) if decision else ())
    return (initial, (first, second), prefix, submit, decision, final, rs)

q = 5
expected = Counter(observe(rs, 7) for rs in product(range(1, q), repeat=4))
assert Counter(observe((a,a,c,c),7) for a,b,c,d in product(range(1,q),repeat=4)) != expected
assert Counter(observe(rs,0) for rs in product(range(1,q),repeat=4)) != expected
assert Counter(x for x in expected if x[4]) != expected
checks = 0
for q in [3,5,7,11]:
    # Legacy fixture enumerates the same units in reverse order.
    legacy = list(range(q-1,0,-1))
    explicit = [i+1 for i in range(q-1)]
    for initial in [0,7]:
        old = Counter(observe(rs,initial) for rs in product(legacy,repeat=4))
        new = Counter(observe(rs,initial) for rs in product(explicit,repeat=4))
        assert old == new
        checks += (q-1)**4
print(json.dumps(dict(nonce_tuples=checks,primes=[3,5,7,11],initial_states=[0,7],
    detected_mutations=['correlated_pairs','reset_initial_state','drop_rejections'],
    failures=0,gaveUp=0),indent=2))
