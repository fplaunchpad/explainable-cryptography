#!/usr/bin/env python3
"""Enumerate reachable shadow-cache transitions against dictionary semantics.

Programming receives an already sampled transcript key/challenge; this gate
checks state handling, not the cryptographic transcript distribution.
"""
import itertools
import json

keys = list(itertools.product(range(2), repeat=2))
actions = list(itertools.product((False, True), keys, range(2)))


def reference(state, action):
    cache, bad, history = state
    program, key, draw = action
    hit = key in cache
    answer = cache.get(key, draw)
    updated = dict(cache)
    updated.setdefault(key, draw)
    return (draw if program else answer,
            (updated, bad or (program and hit),
             [key[0]] + history if program else history))


def finite(state, action, mutation=None):
    entries, bad, history = state
    program, key, draw = action
    found = next((v for k, v in entries if k == key), None)
    hit = found is not None
    updated = entries if hit else [(key, draw)] + entries
    if mutation == 'double_insert' and not hit:
        updated = [(key, draw), (key, draw)] + entries
    if mutation == 'overwrite' and program and hit:
        updated = [(key, draw)] + [(k, v) for k, v in entries if k != key]
    flag = bad or (program and hit)
    if mutation == 'reset' and program:
        flag = hit
    recorded = [key[0]] + history if program else history
    if mutation == 'deduplicate' and program:
        recorded = list(dict.fromkeys(recorded))
    return (draw if program or not hit else found, (updated, flag, recorded))


def agrees(ref, actual):
    return (len(ref[1][0]) == len(actual[1][0]) and
            ref[0] == actual[0] and ref[1] == (
        dict(actual[1][0]), actual[1][1], actual[1][2]))


# Run the same comparison against deliberately broken transitions first.
witnesses = {
    'overwrite': [(True, (0, 0), 0), (True, (0, 0), 1)],
    'double_insert': [(False, (0, 0), 0)],
    'reset': [(True, (0, 0), 0), (True, (0, 0), 0), (True, (1, 0), 1)],
    'deduplicate': [(True, (0, 0), 0), (True, (0, 1), 1)],
}
for mutation, history in witnesses.items():
    ref, actual = ({}, False, []), ([], False, [])
    caught = False
    for action in history:
        r, a = reference(ref, action), finite(actual, action, mutation)
        caught |= not agrees(r, a)
        ref, actual = r[1], a[1]
    assert caught, mutation

frontier = [(({}, False, []), ([], False, []))]
cases = collisions = sticky_fresh = 0
for depth in range(4):
    following = []
    for ref, actual in frontier:
        for action in actions:
            r, a = reference(ref, action), finite(actual, action)
            assert agrees(r, a)
            assert len(a[1][0]) <= depth + 1
            assert len(a[1][2]) <= depth + 1
            assert len(a[1][0]) == len(dict(a[1][0]))
            collisions += action[0] and action[1] in ref[0]
            sticky_fresh += action[0] and ref[1] and action[1] not in ref[0]
            following.append((r[1], a[1]))
            cases += 1
    frontier = following
# Exercise the additive initial offsets separately, including preloaded history
# with duplicate statements. Expected history growth counts source proof requests.
starts = [([], False, []), ([((0, 0), 0)], False, []),
          ([], True, [0, 0]), ([((0, 0), 0), ((1, 0), 1)], True, [1])]
storage_cases = 0
for start in starts:
    initial_cache, initial_history = len(start[0]), len(start[2])
    frontier = [(start, 0)]
    for depth in range(3):
        following = []
        for state, requests in frontier:
            for action in actions:
                _, out = finite(state, action)
                count = requests + int(action[0])
                assert len(out[0]) <= initial_cache + depth + 1
                assert len(out[2]) == initial_history + count
                assert len(out[2]) <= initial_history + depth + 1
                following.append((out, count))
                storage_cases += 1
        frontier = following
print(json.dumps(dict(cases=cases, storage_cases=storage_cases,
                      storage_initial_states=len(starts), programming_collisions=collisions,
                      sticky_fresh=sticky_fresh, detected_mutations=list(witnesses),
                      failures=0, gaveUp=0), indent=2))
