#!/usr/bin/env python3
"""Bounded, independent operational fixtures for raw multi-call execution."""
import itertools
import json
import random


def handler(seed):
    rng = random.Random(seed)
    cache, log = {}, []

    def ask(kind, word=()):
        if kind == 'coin':
            answer = (bool(rng.randrange(2)),)
        else:
            if word not in cache:
                cache[word] = tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(5)))
            answer = cache[word]
        log.append((kind, word, answer))
        return answer
    return ask, log


def source(code, word, seed):
    ask, log = handler(seed)
    tapes, charge = [tuple(word), (True, False)], 0
    for kind, src, dst in code:
        old = tapes[dst]
        if kind == 'hash':
            request = tapes[src]
            answer = ask(kind, request)
            charge += 1 + len(request) + len(old) + len(answer)
        else:
            answer = ask(kind)
            charge += 2 + len(old)
        tapes[dst] = answer
    return tuple(tapes), log, charge


def machine(code, word, seed, mutant=None):
    ask, log = handler(seed)
    tapes = [list(word), [True, False], [], []]
    pc, mode, phase, steps = 0, 'ready', None, 0
    saved = None
    while pc < len(code) or mode != 'ready':
        steps += 1
        assert steps < 1000
        if mode == 'ready':
            kind, src, dst = code[pc]
            saved = pc + 1
            if kind == 'hash':
                mode, phase, roles = 'request', 'clear', (src, 2, 3)
            else:
                tapes[2] = list(ask('coin'))
                mode, phase, roles = 'response', 'clear', (2, dst, 3)
            continue
        if phase is None:
            if mode == 'request':
                tapes[2] = list(ask('hash', tuple(tapes[2])))
                mode, phase, roles = 'response', 'clear', (2, dst, 3)
            else:
                if mutant != 'dirty_private':
                    assert tapes[2] == [] and tapes[3] == []
                pc = saved if mutant != 'skip_successor' else len(code)
                mode = 'ready'
            continue
        a, b, scratch = roles
        if phase == 'done':
            if mode == 'response' and mutant != 'dirty_private' and tapes[a]:
                tapes[a].pop(0)
            else:
                phase = None
            continue
        port = b if phase == 'clear' else a if phase == 'copy' else scratch
        bit = tapes[port].pop(0) if tapes[port] else None
        if phase == 'clear':
            if bit is None:
                phase = 'copy'
                if mode == 'request' and mutant == 'early_query':
                    ask('hash', tuple(tapes[2]))
        elif phase == 'copy':
            if bit is None:
                phase = 'restore'
            else:
                tapes[scratch].insert(0, bit)
        elif phase == 'restore':
            if bit is None:
                phase = 'done'
            else:
                tapes[a].insert(0, bit)
                tapes[b].insert(0, bit)
    return tuple(tuple(t) for t in tapes[:2]), log, steps, tuple(tapes[2]), tuple(tapes[3])


words = [w for n in range(4) for w in itertools.product((False, True), repeat=n)]
operations = [('hash', 0, 0), ('hash', 0, 1), ('hash', 1, 0), ('coin', 0, 1)]
seeds = [7, 19, 41]
cases = 0
for code, word, seed in itertools.product(itertools.product(operations, repeat=3), words, seeds):
    expected, trace, charge = source(code, word, seed)
    result, observed, steps, io, scratch = machine(code, word, seed)
    assert (result, observed, io, scratch) == (expected, trace, (), ())
    assert steps <= 11 * charge
    cases += 1
code = [('hash', 0, 0), ('hash', 0, 1), ('coin', 0, 1)]
expected, trace, _ = source(code, (True, False), 19)
mutants = {}
for mutation in ('early_query', 'dirty_private', 'skip_successor'):
    result, observed, _, io, scratch = machine(code, (True, False), 19, mutation)
    mutants[mutation] = (result, observed, io, scratch) != (expected, trace, (), ())
    assert mutants[mutation]
print(json.dumps(dict(cases=cases, seeds=seeds, source_steps=3, input_lengths=[0, 3],
                     response_lengths=[0, 4], failures=0, gaveUp=0, mutants=mutants), indent=2))
