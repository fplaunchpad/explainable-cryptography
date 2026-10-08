#!/usr/bin/env python3
"""Six explicit binary stacks; independent indexed decoding and integer decrement."""
import itertools
import json


def bits(n):
    return [c == '1' for c in bin(n)[:1:-1]] if n else []


def decrement(tapes, index=4, scratch=2):
    if not tapes[index]:
        return False, 1
    steps = 0
    while True:
        steps += 1
        b = tapes[index].pop(0)
        if b:
            if tapes[index]:
                tapes[index].insert(0, False)
            break
        tapes[scratch].insert(0, True)
    while tapes[scratch]:
        tapes[index].insert(0, tapes[scratch].pop(0))
        steps += 1
    return True, steps+1


def field(tapes, mutant=None):
    source, count = 0, 1
    scratch = 5 if mutant == 'alias_archive' else 2
    output = 3
    steps = 0
    while True:
        steps += 1
        if not tapes[source]:
            return False, steps+1
        if not tapes[source].pop(0):
            break
        tapes[count].append(True)
    while True:
        steps += 1
        if not tapes[count]:
            if tapes[scratch] and not tapes[scratch][0]:
                return False, steps+1
            break
        tapes[count].pop(0)
        if not tapes[source]:
            return False, steps+1
        tapes[scratch].insert(0, tapes[source].pop(0))
    while tapes[scratch]:
        tapes[output].insert(0, tapes[scratch].pop(0))
        steps += 1
    steps += 2  # prefix return, field entry
    while tapes[output]:
        steps += 1
        if not tapes[source]:
            return False, steps+1
        tapes[count].insert(0, tapes[source].pop(0))
        _, used = decrement(tapes, output, scratch)
        steps += used
    steps += 1  # zero counter enters restoration
    while tapes[count]:
        tapes[output].insert(0, tapes[count].pop(0))
        steps += 1
    return True, steps+2  # empty restoration and field final halt


def reference(word):
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
    return list(word[end:end+value]), list(word[end+value:])


def check(word, n, archive, mutant=None):
    outer = bits(n)
    tapes = [list(word), [], [], [], outer.copy(), list(archive)]
    ok, used = field(tapes, mutant)
    assert tapes[4] == outer and tapes[5] == list(archive)
    expected = reference(word)
    assert ok == (expected is not None)
    assert used <= 3*len(word)+5+(len(word)+1)*(2*len(word)+4)
    if ok:
        assert (tapes[3], tapes[0]) == expected and not tapes[1] and not tapes[2]
        before = [x.copy() for x in tapes]
        flag, cost = decrement(tapes, 3 if mutant == 'alias_counter' else 4)
        assert flag == (n != 0) and cost <= 2*n.bit_length()+1
        assert tapes[4] == bits(max(n-1, 0)) and not tapes[2]
        assert all(tapes[k] == before[k] for k in [0, 1, 3, 5])


for mutant, word, n, archive in [
    ('alias_archive', [False], 8, [True, False]),
    ('alias_counter', [True, True, False, False, True, False, True], 8, [True])
]:
    try:
        check(word, n, archive, mutant)
    except (AssertionError, IndexError):
        pass
    else:
        raise AssertionError(f'undetected mutant: {mutant}')
cases = 0
for length in range(9):
    for word in itertools.product([False, True], repeat=length):
        for n in [0, 1, 2, 8, 2**256]:
            for archive in [[], [False], [True, False], [False, True, True]]:
                check(word, n, archive)
                cases += 1
print(json.dumps(dict(cases=cases, failures=0, gaveUp=0, detected_mutants=2,
                     max_raw_length=8, largest_outer_counter_bits=257), indent=2))
