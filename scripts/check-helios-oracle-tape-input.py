#!/usr/bin/env python3
"""Independent physical answer replacement on shared work columns."""
import json
import random


def load(words, port, answer, mutant=None):
    cells = {i: [w[-1-i] if i < len(w) else None for w in words]
             for i in range(max(map(len, words), default=0))}
    native = dict(enumerate(answer))
    wh = ah = used = 0
    phase = 'seekWork'
    while phase != 'done':
        used += 1
        if phase == 'seekWork':
            if cells.get(wh, [None] * len(words))[port] is None:
                phase = 'erase'
            else:
                wh += 1
        elif phase == 'erase':
            if wh == 0:
                phase = 'seekAnswer'
            else:
                wh -= 1
                phase = 'eraseCell'
        elif phase == 'eraseCell':
            if mutant != 'skip_erase':
                cells[wh][port] = None
            phase = 'erase'
        elif phase == 'seekAnswer':
            if native.get(ah) is None:
                phase = 'loadLeft'
            else:
                ah += 1
        elif phase == 'loadLeft':
            ah += 1 if mutant == 'wrong_direction' else -1
            phase = 'write'
        elif phase == 'write':
            bit = native.get(ah)
            if bit is None:
                ah += 1
                phase = 'back'
            else:
                cells.setdefault(wh, [None] * len(words))[port] = bit
                if mutant == 'erase_other':
                    cells[wh][(port + 1) % len(words)] = None
                wh += 1
                phase = 'loadLeft'
        elif wh == 0:
            phase = 'done'
        else:
            wh -= 1
    result = tuple(tuple(reversed([cells[i][k] for i in sorted(cells)
                                   if cells[i][k] is not None])) for k in range(len(words)))
    return result, wh, ah, used, tuple(native[i] for i in sorted(native))


cases, seeds = 0, [7, 19, 41]
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(1800):
        words = [tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(17)))
                 for _ in range(rng.randrange(2, 6))]
        port = rng.randrange(len(words))
        answer = tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(17)))
        expected = list(words)
        expected[port] = answer
        result, wh, ah, used, retained = load(words, port, answer)
        assert result == tuple(expected) and wh == ah == 0 and retained == answer
        assert used == 3 * len(words[port]) + 4 * len(answer) + 6
        cases += 1
words, answer = [(True, True, True, True), (False, True, False, False, True)], (True, False, False)
for mutant in ('skip_erase', 'wrong_direction', 'erase_other'):
    assert load(words, 0, answer, mutant)[0] != (answer, words[1])
assert load(words, 0, (), 'skip_erase')[0][0] != ()
print(json.dumps(dict(cases=cases, seeds=seeds, ports=[2, 5], lengths=[0, 16],
                     failures=0, gaveUp=0, mutants={m: True for m in
                     ('skip_erase', 'wrong_direction', 'erase_other')}), indent=2))
