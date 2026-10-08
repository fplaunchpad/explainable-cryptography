#!/usr/bin/env python3
"""Independent fixed-clock oracle loop versus terminating source execution."""
import itertools
import json
import random


def oracle(seed, limit):
    rng, cache, trace = random.Random(seed), {}, []
    def ask(kind, word=()):
        if kind == 'coin':
            answer = (bool(rng.randrange(2)),)
        else:
            if word not in cache:
                cache[word] = tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(limit + 1)))
            answer = cache[word]
        trace.append((kind, word, answer))
        return answer
    return ask, cache, trace


def reference(code, word, seed, limit):
    ask, cache, trace = oracle(seed, limit)
    tapes, charge = [tuple(word), (True, False)], 1  # final source halt
    for kind, src, dst in code:
        old, request = tapes[dst], tapes[src]
        answer = ask(kind, request) if kind == 'hash' else ask(kind)
        charge += 1 + len(request) + len(old) + len(answer) if kind == 'hash' else 2 + len(old)
        tapes[dst] = answer
    return tuple(tapes), cache, trace, charge


def fixed_clock(code, word, seed, limit, fuel, no_halt=False):
    ask, cache, trace = oracle(seed, limit)
    tapes = [list(word), [True, False], [], []]
    pc, mode, phase = 0, 'ready', None
    halted = False
    for _ in range(fuel):
        if halted:
            continue
        if mode == 'ready':
            if pc == len(code):
                if no_halt:
                    pc = 0
                else:
                    halted = True
                continue
            kind, src, dst = code[pc]
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
                assert tapes[2] == [] and tapes[3] == []
                pc += 1
                mode = 'ready'
            continue
        a, b, scratch = roles
        if phase == 'done':
            if mode == 'response' and tapes[a]:
                tapes[a].pop(0)
            else:
                phase = None
            continue
        port = b if phase == 'clear' else a if phase == 'copy' else scratch
        bit = tapes[port].pop(0) if tapes[port] else None
        if phase == 'clear':
            if bit is None:
                phase = 'copy'
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
    return tuple(tuple(t) for t in tapes[:2]), cache, trace, halted, tuple(tapes[2]), tuple(tapes[3])


words = [w for n in range(4) for w in itertools.product((False, True), repeat=n)]
ops = [('hash', 0, 0), ('hash', 0, 1), ('hash', 1, 0), ('coin', 0, 1)]
seeds, limit, bound = [7, 19, 41], 4, 48
cases = 0
for code, word, seed in itertools.product(itertools.product(ops, repeat=3), words, seeds):
    tapes, cache, trace, charge = reference(code, word, seed, limit)
    assert charge <= bound
    out = fixed_clock(code, word, seed, limit, 11 * bound)
    assert out == (tapes, cache, trace, True, (), ())
    # Padding by another 11*bound must retain both output and handler state.
    assert fixed_clock(code, word, seed, limit, 22 * bound) == out
    cases += 1
code = [('hash', 0, 0), ('hash', 0, 1), ('coin', 0, 1)]
tapes, cache, trace, _ = reference(code, (True, False), 19, limit)
expected = (tapes, cache, trace, True, (), ())
mutants = {
    'missing_halt': fixed_clock(code, (True, False), 19, limit, 11 * bound, no_halt=True) != expected,
    'early_fuel': fixed_clock(code, (True, False), 19, limit, 1) != expected,
}
# A response-size contract cannot be inferred from request/source-step counts.
assert len((True,) * (limit + 1)) > limit
assert all(mutants.values())
print(json.dumps(dict(cases=cases, clocks_per_case=2, seeds=seeds, response_limit=limit,
                     source_bound=bound, clocks=[11 * bound, 22 * bound],
                     failures=0, gaveUp=0, mutants=mutants), indent=2))
