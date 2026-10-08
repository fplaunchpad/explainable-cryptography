#!/usr/bin/env python3
"""Independent head-local export from reversed work columns to an ordinary query tape."""
import json
import random


def export(words, port, reverse_write=False, skip_return=False, previous=None, skip_clear=False):
    cells = {i: tuple(w[-1-i] if i < len(w) else None for w in words)
             for i in range(max(map(len, words), default=0))}
    before = dict(cells)
    query = dict(enumerate(previous or ()))
    wh = qh = steps = 0
    mode = 'copy' if previous is None or skip_clear else 'clear'
    while mode != 'done':
        steps += 1
        if mode == 'clear':
            if query.get(qh) is None:
                mode = 'copy'
            else:
                query[qh] = None
                qh += 1
        elif mode == 'copy':
            bit = cells.get(wh, (None,) * len(words))[port]
            if bit is None:
                qh += -1 if reverse_write else 1
                mode = 'done' if skip_return else 'back'
            else:
                query[qh] = bit
                qh += 1 if reverse_write else -1
                wh += 1
        elif wh == 0:
            mode = 'done'
        else:
            wh -= 1
    query = {i: b for i, b in query.items() if b is not None}
    lo, hi = min(query, default=qh), max(query, default=qh-1)
    out = tuple(query.get(i) for i in range(lo, hi+1))
    return out, wh, qh, lo, steps, cells == before


seeds, cases = [7, 19, 41], 0
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(1800):
        words = [tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(21)))
                 for _ in range(rng.randrange(1, 6))]
        port = rng.randrange(len(words))
        word, wh, qh, lo, ticks, frame = export(words, port)
        assert word == words[port] and wh == 0 and qh == lo and frame
        assert ticks == 2 * len(word) + 2
        previous = tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(21)))
        word, wh, qh, lo, ticks, frame = export(words, port, previous=previous)
        assert word == words[port] and wh == 0 and qh == lo and frame
        assert ticks == len(previous) + 2 * len(word) + 3
        cases += 1
words = [(True, False, False), (False, True, True, False, True)]
assert export(words, 0, reverse_write=True)[0] != words[0]
assert export(words, 0, skip_return=True)[1] != 0
assert export([(), (True, False)], 0, previous=(True, False), skip_clear=True)[0] != ()
print(json.dumps(dict(cases=cases, seeds=seeds, ports=[1, 5], lengths=[0, 20], previous_lengths=[0, 20], runs_per_case=2,
                     failures=0, gaveUp=0,
                     mutants={'rightward_write': True, 'skipped_return': True, 'stale_query_without_clear': True}), indent=2))
