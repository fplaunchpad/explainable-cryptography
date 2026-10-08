#!/usr/bin/env python3
"""Binary decrement transitions against independent integer subtraction."""
import json


def bits(n):
    return tuple(bool((n >> i) & 1) for i in range(n.bit_length()))


def run(n, mutant=None):
    counter, scratch = list(bits(n)), []
    source, frame = (True, False, True), (False, True)
    steps = 0
    while True:
        steps += 1
        if not counter:
            return tuple(counter), tuple(scratch), source, frame, False, steps
        b = counter.pop(0)
        if b:
            if counter or mutant == 'keep_high_zero':
                counter.insert(0, False)
            break
        scratch.insert(0, mutant != 'lose_borrow')
    while scratch:
        counter.insert(0, scratch.pop(0))
        steps += 1
    return tuple(counter), tuple(scratch), source, frame, True, steps + 1


for mutant, n in [('keep_high_zero', 1), ('lose_borrow', 8)]:
    assert run(n, mutant)[0] != bits(n - 1)
values = list(range(4096)) + [2**k for k in range(12, 257)]
for n in values:
    result, scratch, source, frame, flag, steps = run(n)
    assert result == bits(max(n - 1, 0))
    assert scratch == ()
    assert source == (True, False, True) and frame == (False, True)
    assert flag == (n > 0)
    assert steps <= 2 * n.bit_length() + 1
    if n:
        borrow = (n & -n).bit_length() - 1
        assert steps == 2 * borrow + 2
print(json.dumps({'natural_cases': len(values), 'largest_borrow_chain': 256,
                  'detected_mutations': ['keep_high_zero', 'lose_borrow'],
                  'failures': 0, 'gaveUp': 0}, indent=2))
