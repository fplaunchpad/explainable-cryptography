#!/usr/bin/env python3
"""Independent command-tree relocation check; bounded validation, not a proof."""
import itertools
import json
import random


def relocate(cmd, layout, mutant=None):
    tag, *args = cmd
    if tag == 'coin':
        dest, nxt = args
        return tag, layout[dest] if mutant != 'misroute' else layout[-1], nxt
    if tag == 'hash':
        req, dest, nxt = args
        return tag, layout[req] if mutant != 'request' else layout[-1], layout[dest], nxt
    if tag in ('push', 'pop'):
        port, tail = args
        return tag, layout[port], relocate(tail, layout, mutant)
    if tag == 'branch':
        return tag, relocate(args[0], layout, mutant), relocate(args[1], layout, mutant)
    return cmd


def charge(cmd):
    if cmd[0] in ('push', 'pop'):
        return 1 + charge(cmd[2])
    if cmd[0] == 'branch':
        return 1 + max(charge(cmd[1]), charge(cmd[2]))
    return 1


def local(cmd, memory, words):
    tag, *args = cmd
    if tag == 'push':
        words[args[0]].insert(0, memory)
        return local(args[1], memory, words)
    if tag == 'pop':
        memory = words[args[0]].pop(0) if words[args[0]] else False
        return local(args[1], memory, words)
    if tag == 'branch':
        return local(args[0] if memory else args[1], memory, words)
    if tag == 'halt':
        return None, memory, words
    if tag == 'goto':
        return args[0], memory, words
    raise AssertionError(cmd)


def tree(program, fuel, state, replies, append=False):
    label, memory, old = state
    words = [list(w) for w in old]
    if fuel == 0 or label is None:
        return ('leaf', (label, memory, words), 0)
    cmd = program[label]
    if cmd[0] in ('coin', 'hash'):
        if cmd[0] == 'coin':
            _, dest, nxt = cmd
            request, answers = ('coin',), [[False], [True]]
            costs = [2 + len(words[dest])] * 2
        else:
            _, req, dest, nxt = cmd
            request, answers = ('hash', tuple(words[req])), replies
            costs = [1 + len(words[req]) + len(words[dest]) + len(a) for a in answers]
        branches = []
        for answer, cost in zip(answers, costs):
            changed = [list(w) for w in words]
            changed[dest] = list(answer) + (changed[dest] if append else [])
            branches.append(add_cost(tree(program, fuel-1, (nxt, memory, changed), replies, append), cost))
        return ('query', request, branches)
    return add_cost(tree(program, fuel-1, local(cmd, memory, words), replies, append), charge(cmd))


def add_cost(node, amount):
    if node[0] == 'leaf':
        return node[0], node[1], node[2] + amount
    return node[0], node[1], [add_cost(b, amount) for b in node[2]]


def embed_tree(node, layout, frame):
    if node[0] == 'query':
        return node[0], node[1], [embed_tree(b, layout, frame) for b in node[2]]
    label, memory, words = node[1]
    combined = [None] * len(layout)
    for index, word in enumerate(words + frame):
        combined[layout[index]] = word
    return node[0], (label, memory, combined), node[2]


def check(layout, words, frame, memory, fuel, mutant=None):
    # Query aliases and a local branch exercise overwritten, retained and empty words.
    program = [('coin', 1, 1), ('hash', 1, 0, 2),
               ('pop', 0, ('branch', ('push', 1, ('halt',)), ('goto', 0)))]
    replies = [[], [False, True], [True, False, True]]
    original = tree(program, fuel, (0, memory, words), replies)
    initial = embed_tree(('leaf', (0, memory, words), 0), layout, frame)[1]
    actual = tree([relocate(c, layout, mutant) for c in program], fuel, initial,
                  replies, append=mutant == 'append')
    return actual == embed_tree(original, layout, frame)


def main():
    words = [[], [False], [True, False]]
    count = 0
    for layout in itertools.permutations(range(3)):
        for x, y, private in itertools.product(words, repeat=3):
            for memory in (False, True):
                for fuel in range(7):
                    assert check(layout, [x, y], [private], memory, fuel)
                    count += 1
    seeded = 0
    for seed in (7, 19, 41):
        rng = random.Random(seed)
        for _ in range(200):
            layout = list(range(6)); rng.shuffle(layout)
            records = [[bool(rng.getrandbits(1)) for _ in range(rng.randrange(33))] for _ in range(6)]
            assert check(layout, records[:2], records[2:], bool(rng.getrandbits(1)), rng.randrange(8))
            seeded += 1
    mutations = ['misroute', 'request', 'append']
    for mutant in mutations:
        assert not check([2, 0, 1], [[True, False], [True]], [[False, False, True]], False, 4, mutant)
    print(json.dumps({'exhaustive': count, 'seeded': seeded, 'seeds': [7,19,41],
                      'mutations_detected': mutations, 'failures': 0, 'gaveUp': 0}, indent=2))


if __name__ == '__main__':
    main()
