#!/usr/bin/env python3
"""Finite parser transitions checked against independent integer prefix decoding."""
import itertools
import json


def machine(word, mutant=None):
    source, count, scratch, output = list(word), [], [], []
    steps = 0
    while True:
        steps += 1
        if not source:
            return None, steps
        b = source.pop(0)
        if not b:
            break
        count.append(True)
    while True:
        steps += 1
        if not count:
            if scratch and not scratch[0] and mutant != 'allow_high_zero':
                return None, steps
            break
        count.pop()
        if not source:
            if mutant != 'pad_truncation':
                return None, steps
            b = True
        else:
            b = source.pop(0)
        scratch.insert(0, b)
    while scratch:
        output.insert(0, scratch.pop(0))
        steps += 1
    return (tuple(output), tuple(source)), steps + 1


def reference(word):
    try:
        width = word.index(False)
    except ValueError:
        return None
    end = 2 * width + 1
    if len(word) < end:
        return None
    payload = word[width + 1:end]
    value = sum(int(b) * 2**i for i, b in enumerate(payload))
    if value.bit_length() != width:
        return None
    return payload, word[end:]


for mutant, word in [('allow_high_zero', (True, False, False)),
                     ('pad_truncation', (True, False))]:
    assert machine(word, mutant)[0] != reference(word)
cases = 0
for size in range(13):
    for word in itertools.product((False, True), repeat=size):
        result, steps = machine(word)
        assert result == reference(word)
        assert steps <= 3 * len(word) + 3
        if result is not None:
            assert steps == 3 * len(result[0]) + 3
        cases += 1
print(json.dumps({'raw_words': cases, 'maximum_length': 12,
                  'detected_mutations': ['allow_high_zero', 'pad_truncation'],
                  'failures': 0, 'gaveUp': 0}, indent=2))
