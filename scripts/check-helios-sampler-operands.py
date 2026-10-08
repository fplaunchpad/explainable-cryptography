#!/usr/bin/env python3
"""Serialized operand preparation: finite stack steps versus integer/reference parsing."""
import itertools
import json
import random
from pathlib import Path


def bits(n):
    return [bool((n >> i) & 1) for i in range(n.bit_length())]


def encode(slack, n, suffix):
    return [True]*slack + [False] + [True]*n.bit_length() + [False] + bits(n) + suffix


def execute(mode, raw, frame, mutant=None):
    w = [[], [], [], [], list(raw), *map(list, frame)]
    phase, value, ticks = 'slack', None, 0
    def pop(i):
        return w[i].pop(0) if w[i] else None
    while phase is not None:
        ticks += 1
        assert ticks <= 20*len(raw)+40
        if phase == 'slack':
            value = pop(4)
            if value is None: value, phase = False, None
            elif value:
                if mutant != 'lost_slack': w[2].insert(0, True)
            else: phase = 'width'
        elif phase == 'width':
            value = pop(4)
            if value is None: value, phase = False, 'parsed'
            elif value: w[0].insert(0, True)
            else: phase = 'payload'
        elif phase == 'payload':
            value = pop(0)
            if value is not None:
                value = pop(4)
                if value is None: value, phase = False, 'parsed'
                else: w[3].insert(0, value)
            else:
                value = w[3][0] if w[3] else None
                if value is False: value, phase = False, 'parsed'
                else: phase = 'parser_restore'
        elif phase == 'parser_restore':
            value = pop(3)
            if value is None: value, phase = True, 'parsed'
            else: w[1].insert(0, value)
        elif phase == 'parsed':
            if value is not True: value, phase = False, None
            else: phase = 'increment' if mode and mutant != 'skip_increment' else 'ready'
        elif phase == 'increment':
            value = pop(1)
            if value: w[3].insert(0, False)
            else: w[1].insert(0, True); phase = 'carry_restore'
        elif phase == 'carry_restore':
            value = pop(3)
            if value is None: value, phase = True, 'ready'
            else: w[1].insert(0, value)
        elif phase == 'ready':
            value = w[1][0] if w[1] else None
            if value is None: value, phase = False, None
            else: phase = 'collect'
        elif phase == 'collect':
            value = pop(1)
            if value is None: phase = 'restore'
            else: w[3].insert(0, value); w[2].insert(0, True)
        elif phase == 'restore':
            value = (w[3].pop() if w[3] else None) if mutant == 'reverse' else pop(3)
            if value is None: phase = None
            else: w[1].insert(0, value)
        else: raise AssertionError(phase)
    return value is None, w, ticks


def reference(mode, raw):
    try:
        slack = raw.index(False)
        rest = raw[slack+1:]
        width = rest.index(False)
    except ValueError:
        return None
    payload = rest[width+1:]
    if len(payload) < width: return None
    ds = payload[:width]
    if ds and not ds[-1]: return None
    n = sum(int(b) << i for i, b in enumerate(ds))
    q = n+1 if mode else n
    if not q: return None
    return slack, q, payload[width:]


def check(mode, raw, frame, mutant=None):
    result, w, ticks = execute(mode, raw, frame, mutant)
    ref = reference(mode, raw)
    assert result == (ref is not None)
    assert w[5:] == frame
    if ref:
        slack, q, suffix = ref
        assert w == [[], bits(q), [True]*(q.bit_length()+slack), [], suffix, *frame]
        n = q-1 if mode else q
        bound = slack+5*n.bit_length()+(2*q.bit_length()+10 if mode else 8)
        assert ticks <= bound
    return result


for mutant in ['skip_increment', 'lost_slack', 'reverse']:
    try:
        check(True, encode(2, 5, [False, True]), [[True], [False], [True, False]], mutant)
    except AssertionError: pass
    else: raise AssertionError('undetected '+mutant)
valid = 0
for mode, n, slack, suffix in itertools.product([False, True], range(129), range(9),
                                               [[], [True], [False, True]]):
    check(mode, encode(slack, n, suffix), [[True, False], [], [False]])
    valid += 1
raw_count = 0
for mode in [False, True]:
    for length in range(11):
        for raw in itertools.product([False, True], repeat=length):
            check(mode, list(raw), [[False], [True, False], [True]])
            raw_count += 1
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(250):
        n = rng.getrandbits(rng.randrange(129))
        suffix = [bool(rng.getrandbits(1)) for _ in range(rng.randrange(20))]
        frame = [[bool(rng.getrandbits(1)) for _ in range(rng.randrange(12))] for _ in range(3)]
        check(bool(rng.getrandbits(1)), encode(rng.randrange(129), n, suffix), frame)
report = dict(canonical=valid, raw=raw_count, seeded=750, seeds=[7,19,41],
              max_seeded_bits=128, max_seeded_slack=128,
              mutants=['skip_increment','lost_slack','reverse'], failures=0, gaveUp=0)
Path('tmp/concrete-helios/sampler-operands-fixtures.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
