#!/usr/bin/env python3
"""Loaded scalar digits: actual three writer loops versus integer prefix encoding."""
import itertools
import json
import random


def bits(n):
    return [bool((n >> i) & 1) for i in range(n.bit_length())]


def execute(n, modulus, suffix, mutant=None):
    # Remainder, modulus, carry, reverse buffer, input, output, two frame ports.
    words = [bits(n), list(modulus), [], [], [], list(suffix), [True, False], [False]]
    ticks = 0
    while words[0]:
        words[3].insert(0, words[0].pop(0))
        words[2].insert(0, True)
        ticks += 1
    ticks += 1
    while words[3]:
        words[5].insert(0, words[3].pop(-1 if mutant == 'reverse' else 0))
        ticks += 1
    if mutant != 'delimiter':
        words[5].insert(0, False)
    ticks += 1
    while words[2]:
        words[2].pop(0)
        words[5].insert(0, True)
        ticks += 1
    ticks += 1
    return words, ticks


def check(n, modulus, suffix, mutant=None):
    words, ticks = execute(n, modulus, suffix, mutant)
    assert words == [[], list(modulus), [], [], [],
                     [True]*n.bit_length()+[False]+bits(n)+list(suffix),
                     [True, False], [False]]
    assert ticks == 3*n.bit_length()+3


for mutant, n in [('reverse', 2), ('delimiter', 0)]:
    try:
        check(n, [True, True], [], mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant '+mutant)
count = 0
for n in range(256):
    for width in range(4):
        for suffix in itertools.product([False, True], repeat=width):
            check(n, bits(257), list(suffix))
            count += 1
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(250):
        check(rng.getrandbits(rng.randrange(257)),
              [bool(rng.randrange(2)) for _ in range(rng.randrange(129))],
              [bool(rng.randrange(2)) for _ in range(rng.randrange(129))])
print(json.dumps(dict(exhaustive=count, seeded=750, seeds=[7,19,41],
                      directed_zero=True, max_scalar_bits=256,
                      detected_mutants=['reverse','delimiter'], failures=0, gaveUp=0), indent=2))
