#!/usr/bin/env python3
"""Independent complete-stack fixtures for the two-pass copy operation."""
import itertools
import json


def copy_machine(word, suffix, mutant=None):
    source, dest, scratch = list(word), list(suffix), []
    steps = 0
    while source:
        scratch.insert(0, source.pop(0))
        steps += 1
    steps += 1
    while scratch:
        bit = scratch.pop(0)
        if mutant != 'erased_source':
            source.insert(0, bit)
        if mutant == 'reversed_copy':
            dest.append(bit)
        else:
            dest.insert(0, bit)
        steps += 1
    return tuple(source), tuple(dest), tuple(scratch), steps + 1


words = [w for n in range(7) for w in itertools.product((False, True), repeat=n)]
for mutant in ('reversed_copy', 'erased_source'):
    assert copy_machine((True, False), (), mutant) != (
        (True, False), (True, False), (), 6)
count = 0
for word in words:
    for suffix in words:
        assert copy_machine(word, suffix) == (word, word + suffix, (), 2 * len(word) + 2)
        count += 1
print(json.dumps({'word_suffix_pairs': count, 'maximum_length': 6,
                  'detected_mutations': ['reversed_copy', 'erased_source'],
                  'failures': 0, 'gaveUp': 0}, indent=2))
