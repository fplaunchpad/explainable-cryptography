#!/usr/bin/env python3
"""Independent persistent tape runs against finite direct stack execution."""
import random
import json


def accesses(q):
    op = q[0]
    if op in ('push', 'peek', 'pop'):
        return 1 + accesses(q[2])
    if op == 'load':
        return accesses(q[2])
    if op == 'branch':
        return max(accesses(q[1]), accesses(q[2]))
    return 0


def source(code, words, memory, label, fuel):
    words = [list(w) for w in words]
    for _ in range(fuel):
        if label is None:
            continue
        q = code[label]
        while True:
            op = q[0]
            if op in ('halt', 'goto'):
                label = None if op == 'halt' else q[1]
                break
            if op == 'branch':
                q = q[1] if memory else q[2]
            elif op == 'load':
                memory, q = q[1:]
            else:
                k, tail = q[1:]
                if op == 'push':
                    words[k].insert(0, memory)
                else:
                    memory = words[k][0] if words[k] else False
                    if op == 'pop' and words[k]:
                        words[k].pop(0)
                q = tail
    return tuple(tuple(w) for w in words), memory, label


def tape(code, words, memory, label, fuel, wrong_order=False):
    cells = {}
    for k, w in enumerate(words):
        for n, bit in enumerate(w if wrong_order else reversed(w)):
            cells.setdefault(n, [None, None])[k] = bit
    state, head, used, boundaries = ('normal', label), 0, 0, 0
    while boundaries < fuel and label is not None:
        used += 1
        assert used < 10000
        mode, *args = state
        if mode == 'go':
            op, k, tail = args
            if cells.get(head, [None, None])[k] is not None:
                head += 1
                continue
            if op == 'push':
                cells.setdefault(head, [None, None])[k] = memory
                head += 1
            elif op == 'peek':
                bit = cells.get(head - 1, [None, None])[k]
                memory = bit if bit is not None else False
            elif op == 'pop':
                if head == 0:
                    memory = False
                else:
                    head -= 1
                    memory = cells[head][k]
                    cells[head][k] = None
            state = ('ret', tail)
            continue
        if mode == 'ret':
            if head != 0:
                head -= 1
                continue
            q = args[0]
        else:
            q = code[label]
        while q[0] in ('branch', 'load'):
            if q[0] == 'branch':
                q = q[1] if memory else q[2]
            else:
                memory, q = q[1:]
        if q[0] in ('halt', 'goto'):
            label = None if q[0] == 'halt' else q[1]
            state = ('normal', label)
            boundaries += 1
        else:
            state = ('go', q[0], q[1], q[2])
    out = tuple(tuple(reversed([cells[n][k] for n in sorted(cells) if cells[n][k] is not None])) for k in range(2))
    return (out, memory, label), head, used


def statement(rng, depth):
    op = rng.choice(('halt', 'goto')) if depth == 0 else rng.choice(('push', 'peek', 'pop', 'load', 'branch', 'halt', 'goto'))
    if op == 'halt':
        return (op,)
    if op == 'goto':
        return (op, rng.randrange(2))
    if op == 'branch':
        return (op, statement(rng, depth - 1), statement(rng, depth - 1))
    return (op, bool(rng.randrange(2)) if op == 'load' else rng.randrange(2), statement(rng, depth - 1))


cases, seeds = 0, [7, 19, 41]
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(1500):
        code = [statement(rng, 5) for _ in range(2)]
        words = [tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(7))) for _ in range(2)]
        memory, label, fuel = bool(rng.randrange(2)), rng.choice((None, 0, 1)), rng.randrange(9)
        expected = source(code, words, memory, label, fuel)
        result, head, used = tape(code, words, memory, label, fuel)
        A, H = max(map(accesses, code)), max(map(len, words))
        assert result == expected and head == 0
        assert max(map(len, result[0])) <= H + fuel * A
        assert used <= fuel * (1 + A * (2 * (H + fuel * A) + 2))
        cases += 1
code = [('push', 0, ('goto', 0))]
result, head, used = tape(code, [(), ()], True, 0, 4)
assert result == (((True,) * 4, ()), True, 0) and head == 0 and used == 28
assert used > 4 * (1 + (2 * (0 + 1) + 2))  # frozen initial height is false
code = [('peek', 0, ('halt',))]
words = [(True, False, False), (False, True)]
expected = source(code, words, False, 0, 1)
assert tape(code, words, False, 0, 1, wrong_order=True)[0] != expected
print(json.dumps(dict(cases=cases, seeds=seeds, labels=2, depth=5, stack_lengths=[0, 6],
                     source_fuel=[0, 8], failures=0, gaveUp=0,
                     mutants={'frozen_initial_height': True, 'unreversed_columns': True}), indent=2))
