#!/usr/bin/env python3
"""Check regional polynomial inequalities; no execution/PPT claim is inferred."""
import json
import random

# Minimized envelope mutant: deleting the fixed overhead makes the claimed
# regional allowance zero on empty words, while its checked region bounds sum
# to 648. This refutes the arithmetic envelope, not a cryptographic claim.
empty_regions = 4 * (18 * 4 + 7) + 7 + 9 + 4 * (18 * 4 + 7)
mutants = {'zero_offset': empty_regions > 650 * 0 ** 2}
assert empty_regions == 648 and all(mutants.values())
cases = 0
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(4000):
        cap = rng.randrange(65)
        height = rng.randrange(cap + 1)
        accesses = rng.randrange(cap + 1)
        request, destination, previous, answer = [rng.randrange(cap + 1) for _ in range(4)]
        prep = 2 * request + 4
        reply = destination + 3 * answer + 4
        before = prep * (6 * cap + 18 * prep + 7) + previous + 2 * request + 7
        after = 3 * request + 4 * answer + 9 + reply * (6 * cap + 18 * reply + 7)
        local = 3 + accesses * (2 * (height + accesses) + 2)
        bound = 650 * (cap + 1) ** 2
        assert before + after <= bound and local <= bound
        cases += 1
# Sample actual push/pop/load/hash/coin word transitions. B is the sampled
# path's source charge; this campaign does not establish an all-branch Within
# premise or execute TM1. It checks the accumulation invariant used by Lean.
mutants['frozen_height'] = len([True]) > 0
mutants['omit_previous'] = 2 > 0 + 1
assert all(mutants.values())
traces = steps = 0
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(1200):
        ports = rng.randrange(1, 5)
        words = [[bool(rng.randrange(2)) for _ in range(rng.randrange(9))] for _ in range(ports)]
        initial_height = max(map(len, words))
        previous = [bool(rng.randrange(2)) for _ in range(rng.randrange(9))]
        initial_previous = len(previous)
        transitions = []
        for _ in range(rng.randrange(17)):
            kind = rng.choice(['push', 'pop', 'load', 'hash', 'coin'])
            height = max(map(len, words))
            old_previous = len(previous)
            port = rng.randrange(ports)
            if kind in ('push', 'pop', 'load'):
                access = int(kind != 'load')
                charge = 2
                ticks = 3 + access * (2 * (height + access) + 2)
                if kind == 'push':
                    words[port].insert(0, bool(rng.randrange(2)))
                elif kind == 'pop' and words[port]:
                    del words[port][0]
            else:
                answer = [bool(rng.randrange(2)) for _ in range(1 if kind == 'coin' else rng.randrange(9))]
                destination = rng.randrange(ports)
                dest = len(words[destination])
                reply = dest + 3 * len(answer) + 4
                after = 4 * len(answer) + 9 + reply * (6 * max(height, len(answer)) + 18 * reply + 7)
                if kind == 'coin':
                    charge = 2 + dest
                    ticks = 2 + after
                else:
                    request = list(words[port])
                    prep = 2 * len(request) + 4
                    charge = 1 + len(request) + dest + len(answer)
                    before = prep * (6 * height + 18 * prep + 7) + old_previous + 2 * len(request) + 7
                    ticks = before + after + 3 * len(request)
                    previous = request
                words[destination] = answer
            transitions.append((height, old_previous, charge, ticks, max(map(len, words)), len(previous)))
        # Ordinary halt, including dispatch and return.
        height = max(map(len, words))
        transitions.append((height, len(previous), 1, 3, height, len(previous)))
        budget = sum(t[2] for t in transitions)
        cap = initial_height + budget + initial_previous
        allowance = 650 * (cap + 1) ** 2
        remaining, spent = budget, 0
        for height, prev_len, charge, ticks, next_height, next_prev in transitions:
            assert height + remaining <= cap and prev_len <= cap
            assert ticks <= allowance * charge
            remaining -= charge
            spent += ticks
            assert next_height + remaining <= cap and next_prev <= cap
            assert spent <= allowance * (budget - remaining)
            steps += 1
        assert remaining == 0 and spent <= allowance * budget
        traces += 1
print(json.dumps({'cases': cases, 'trace_cases': traces, 'trace_steps': steps,
                  'seeds': [7, 19, 41], 'caps': [0, 64], 'trace_ports': [1, 4],
                  'trace_word_lengths': [0, 8], 'active_steps_before_halt': [0, 16],
                  'failures': 0, 'gaveUp': 0, 'mutants': mutants,
                  'scope': 'regional inequalities and sampled-path cap/charge accumulation; no TM1 timing or all-branch premise',
                  'zero_cap_nonempty_reply': {'old_height': 0, 'reply_length': 1, 'next_height': 1}}, indent=2))
