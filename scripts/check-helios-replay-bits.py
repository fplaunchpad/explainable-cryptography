#!/usr/bin/env python3
"""Independent mixed saved-tape codec gate; reuses checked natural fixtures."""
import contextlib
import io
import itertools
import json
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    base = runpy.run_path('scripts/check-helios-uniform-codec.py')
enc_nat, read_nat, uniform_decode = base['encode_nat'], base['read_nat'], base['decode']


def event_encode(e):
    if e[0] == 'uniform':
        return [0] + enc_nat(e[1]) + enc_nat(e[2])
    return [1] + enc_nat(e[1])


def event_decode(word, q, mutation=None):
    if not word:
        return None
    tag = 1 - word[0] if mutation == 'swap_tags' else word[0]
    if tag == 0:
        answer = uniform_decode(word[1:])
        return None if answer is None else ('uniform', *answer)
    answer = read_nat(word[1:])
    if answer is None or answer[1]:
        return None
    a = answer[0]
    if a >= q and mutation != 'reduce_scalar':
        return None
    return ('hash', a % q)


def encode(tape):
    out = enc_nat(len(tape))
    for e in tape:
        word = event_encode(e)
        out += enc_nat(len(word)) + word
    return out


def decode(word, q, mutation=None):
    first = read_nat(word)
    if first is None:
        return None
    count, rest = first
    tape = []
    for _ in range(count):
        framed = read_nat(rest)
        if framed is None:
            return None
        size, payload = framed
        if size > len(payload):
            return None
        event = event_decode(payload[:size], q, mutation)
        if event is None:
            return None
        tape.append(event)
        rest = payload[size:]
    if rest and mutation != 'trailing':
        return None
    return tape


assert encode([]) == [0]
for q in (3, 11):
    overflow = [1] + enc_nat(q)
    bad = enc_nat(1) + enc_nat(len(overflow)) + overflow
    assert decode(bad, q) is None and decode(bad, q, 'reduce_scalar') == [('hash', 0)]
    word = encode([('uniform', 0, 0), ('hash', 0)])
    assert decode(word, q, 'swap_tags') != [('uniform', 0, 0), ('hash', 0)]
    assert decode(encode([]) + [0], q) is None
    assert decode(encode([]) + [0], q, 'trailing') == []
valid = malformed = 0
for q in (3, 11):
    events = [('uniform', n, a) for n in range(4) for a in range(n + 1)]
    events += [('hash', a) for a in (0, 1, q - 1)]
    for size in range(4):
        for tape in itertools.product(events, repeat=size):
            tape = list(tape)
            word = encode(tape)
            assert decode(word, q) == tape
            expected = len(enc_nat(size)) + sum(len(enc_nat(len(event_encode(e)))) + len(event_encode(e)) for e in tape)
            assert len(word) == expected
            assert decode(word[:-1], q) is None
            frames = word[len(enc_nat(size)):]
            assert decode(enc_nat(size + 1) + frames, q) is None
            malformed += 2
            if size:
                assert decode(enc_nat(size - 1) + frames, q) is None
                malformed += 1
            valid += 1
words = accepted = 0
for size in range(15):
    for bits in itertools.product((0, 1), repeat=size):
        word = list(bits)
        tape = decode(word, 3)
        if tape is not None:
            assert encode(tape) == word
            accepted += 1
        words += 1
print(json.dumps(dict(valid_tapes=valid, malformed_variants=malformed, arbitrary_words=words,
                      accepted_canonical_words=accepted, scalar_moduli=[3, 11],
                      detected_mutations=['reduce_scalar', 'swap_tags', 'trailing'],
                      failures=0, gaveUp=0), indent=2))
