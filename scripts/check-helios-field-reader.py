#!/usr/bin/env python3
"""Independent integer slicing oracle for binary-counter field execution."""
import itertools
import json


def bits(n):
    return [c == '1' for c in bin(n)[:1:-1]] if n else []


def machine(n, word, mutant=None, initial_bits=None):
    counter = bits(n) if initial_bits is None else list(initial_bits)
    source, collected, scratch = list(word), [], []
    steps = 0
    while True:
        steps += 1  # read: check counter, then consume input, then call borrow
        if not counter:
            output = []
            while collected:
                steps += 1
                output.insert(0, collected.pop(0))
            steps += 1
            if mutant == 'reverse':
                output.reverse()
            return True, output, source, counter, scratch, steps
        if not source:
            return mutant == 'pad_short', [], source, counter, scratch, steps
        collected.insert(0, source.pop(0))
        while True:
            steps += 1
            bit = counter.pop(0)
            if bit:
                if counter:
                    counter.insert(0, False)
                break
            scratch.insert(0, True)
        while scratch:
            steps += 1
            counter.insert(0, scratch.pop(0))
        steps += 1  # empty scratch returns to read


def check(n, word, mutant=None):
    ok, output, suffix, counter, scratch, steps = machine(n, word, mutant)
    expected = n <= len(word)
    assert ok == expected
    assert not scratch
    if expected:
        assert output == list(word[:n]) and suffix == list(word[n:])
        assert counter == []
    else:
        assert not suffix and counter == bits(n-len(word))
    assert steps <= (min(n, len(word))+1)*(2*n.bit_length()+4)


for mutant, n, word in [('reverse', 2, [False, True]), ('pad_short', 1, [])]:
    try:
        check(n, word, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError(f'undetected mutant: {mutant}')
count = 0
for length in range(9):
    for word in itertools.product([False, True], repeat=length):
        for n in range(12):
            check(n, word)
            count += 1
for exponent in range(12, 257):
    for word in [[], [True], [False, True, False]]:
        check(2**exponent, word)
        count += 1


def raw_machine(word, mutant=None):
    source, count, scratch, output = list(word), [], [], []
    steps = 0
    while True:
        steps += 1
        if not source:
            return None, steps+1
        if not source.pop(0):
            break
        count.append(True)
    while True:
        steps += 1
        if not count:
            if scratch and not scratch[0]:
                return None, steps+1
            break
        count.pop()
        if not source:
            return None, steps+1
        scratch.insert(0, source.pop(0))
    while scratch:
        output.insert(0, scratch.pop(0))
        steps += 1
    steps += 2  # prefix return and enter field control
    ok, field, suffix, _, _, used = machine(0, source, mutant, output)
    return (tuple(field), tuple(suffix)) if ok else None, steps+used+1


def raw_reference(word):
    try:
        width = word.index(False)
    except ValueError:
        return None
    end = 2*width+1
    if end > len(word):
        return None
    value = sum(int(b)*2**i for i, b in enumerate(word[width+1:end]))
    if value.bit_length() != width or value > len(word)-end:
        return None
    return tuple(word[end:end+value]), tuple(word[end+value:])


for mutant, word in [('reverse', [True, True, False, False, True, False, True]),
                     ('pad_short', [True, False, True])]:
    assert raw_machine(word, mutant)[0] != raw_reference(word)
raw_count = 0
for length in range(13):
    for word in itertools.product([False, True], repeat=length):
        actual, used = raw_machine(word)
        assert actual == raw_reference(word)
        assert used <= 3*length+5+(length+1)*(2*length+4)
        raw_count += 1
print(json.dumps(dict(counter_cases=count, raw_words=raw_count, failures=0,
                     gaveUp=0, counter_mutants_detected=2, raw_mutants_detected=2,
                     largest_counter_bits=257), indent=2))
