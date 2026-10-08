#!/usr/bin/env python3
"""Independent canonical uniform-event bit fixtures and malformed-word gate."""
import itertools
import json


def digits(n):
    return [(n >> i) & 1 for i in range(n.bit_length())]


def encode_nat(n):
    bits = digits(n)
    return [1] * len(bits) + [0] + bits


def read_nat(word, canonical=True):
    width = 0
    while width < len(word) and word[width] == 1:
        width += 1
    if width == len(word):
        return None
    start = width + 1
    if start + width > len(word):
        return None
    bits = word[start:start + width]
    value = sum(b << i for i, b in enumerate(bits))
    if canonical and digits(value) != bits:
        return None
    return value, word[start + width:]


def decode(word, mutation=None):
    first = read_nat(word, mutation != 'padding')
    if first is None:
        return None
    n, rest = first
    second = read_nat(rest, mutation != 'padding')
    if second is None:
        return None
    answer, suffix = second
    if suffix and mutation != 'trailing':
        return None
    if answer > n and mutation != 'range':
        return None
    return n, answer


assert encode_nat(0) == [0]
assert encode_nat(1) == [1, 0, 1]
assert encode_nat(2) == [1, 1, 0, 0, 1]
for mutant, word in [('padding', [1, 0, 0, 0]),
                     ('trailing', [0, 0, 1]),
                     ('range', [0, 1, 0, 1])]:
    assert decode(word) is None and decode(word, mutant) is not None
valid = 0
for n in range(65):
    for a in range(n + 1):
        word = encode_nat(n) + encode_nat(a)
        assert decode(word) == (n, a)
        assert len(word) == 2 * n.bit_length() + 2 * a.bit_length() + 2
        for suffix in ([], [0], [1, 0, 1]):
            assert read_nat(encode_nat(n) + suffix) == (n, suffix)
        valid += 1
words = accepted = 0
for size in range(13):
    for bits in itertools.product((0, 1), repeat=size):
        word = list(bits)
        result = decode(word)
        if result is not None:
            n, a = result
            assert a <= n and word == encode_nat(n) + encode_nat(a)
            accepted += 1
        words += 1
print(json.dumps(dict(valid_events=valid, arbitrary_words=words,
                      accepted_canonical_words=accepted,
                      detected_mutations=['padding', 'trailing', 'range'],
                      failures=0, gaveUp=0), indent=2))
