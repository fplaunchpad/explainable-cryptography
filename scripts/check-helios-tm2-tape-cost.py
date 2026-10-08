#!/usr/bin/env python3
"""Independent finite tape interpretation of the existing TM2-to-TM1 design."""
import json
import random


def actions(q):
    op, *args = q
    if op in ('push', 'pop', 'peek'):
        return 1 + actions(args[-1])
    if op == 'load':
        return actions(args[-1])
    if op == 'branch':
        return max(actions(args[0]), actions(args[1]))
    return 0


def source(q, words, v):
    words = [list(w) for w in words]
    while True:
        op, *args = q
        if op in ('halt', 'goto'):
            return tuple(tuple(w) for w in words), v, None if op == 'halt' else 7
        if op == 'load':
            v, q = args
        elif op == 'branch':
            q = args[0] if v else args[1]
        else:
            k, q = args
            if op == 'push':
                words[k].insert(0, bool(v))
            else:
                v = words[k][0] if words[k] else False
                if op == 'pop' and words[k]:
                    words[k].pop(0)


def tape_run(q, words, v, mutant=None):
    cells = {}
    for k, w in enumerate(words):
        for n, bit in enumerate(reversed(w)):
            cells.setdefault(n, [None, None])[k] = bit
    head, state, ticks = 0, ('normal', q), 0
    while True:
        ticks += 1
        assert ticks < 1000
        mode, *args = state
        if mode == 'go':
            op, k, tail = args
            if cells.get(head, [None, None])[k] is not None:
                head += 1
                continue
            if op == 'push':
                if mutant == 'erase_other_port':
                    cells[head] = [None, None]
                cells.setdefault(head, [None, None])[k] = bool(v)
                head += 1
            elif op == 'peek':
                head -= 1
                bit = cells.get(head, [None, None])[k]
                v = bit if bit is not None else False
                head += 1
            elif op == 'pop':
                if head == 0:
                    v = False
                else:
                    head -= 1
                    v = cells.get(head, [None, None])[k]
                    cells[head][k] = None
            state = ('ret', tail)
            continue
        if mode == 'ret':
            tail, = args
            if head != 0 and mutant != 'skip_return':
                head -= 1
                continue
            q = tail
        else:
            q, = args
        # trNormal groups finite local load/branch syntax in the current TM1 tick.
        while q[0] in ('load', 'branch'):
            if q[0] == 'load':
                _, v, q = q
            else:
                q = q[1] if v else q[2]
        if q[0] in ('halt', 'goto'):
            out = []
            for k in range(2):
                col = [cells[n][k] for n in sorted(cells) if cells[n][k] is not None]
                out.append(tuple(reversed(col)))
            return (tuple(out), v, None if q[0] == 'halt' else 7), head, ticks
        op, k, tail = q
        state = ('go', op, k, tail)


def statement(rng, depth):
    if depth == 0:
        return (rng.choice(('halt', 'goto')),)
    op = rng.choice(('push', 'pop', 'peek', 'load', 'branch', 'halt', 'goto'))
    if op == 'branch':
        return (op, statement(rng, depth - 1), statement(rng, depth - 1))
    if op in ('halt', 'goto'):
        return (op,)
    return (op, rng.randrange(2), statement(rng, depth - 1))


seeds, cases = [7, 19, 41], 0
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(2000):
        q = statement(rng, 6)
        words = [tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(9))) for _ in range(2)]
        v = bool(rng.randrange(2))
        expected = source(q, words, v)
        result, head, ticks = tape_run(q, words, v)
        a, height = actions(q), max(map(len, words))
        assert result == expected and head == 0
        assert ticks <= 1 + a * (2 * (height + a) + 2)
        cases += 1
q, words = ('push', 0, ('peek', 0, ('halt',))), [(True, False), (False, True, False, True)]
expected = source(q, words, True)
mutants = {}
for mutation in ('skip_return', 'erase_other_port'):
    result, head, _ = tape_run(q, words, True, mutation)
    mutants[mutation] = result != expected or head != 0
    assert mutants[mutation]
_, _, ticks = tape_run(('peek', 0, ('halt',)), [(True,) * 8, ()], False)
assert ticks > 1 + actions(('peek', 0, ('halt',))) * 3
print(json.dumps(dict(cases=cases, seeds=seeds, depth=6, stack_lengths=[0, 8],
                     failures=0, gaveUp=0, mutants=mutants, constant_cost_refuted=True), indent=2))
