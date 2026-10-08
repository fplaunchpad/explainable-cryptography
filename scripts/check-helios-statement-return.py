#!/usr/bin/env python3
"""Independent source/finite-return interpreters; this does not measure TM1 cost."""
import json
import random


def source(q, memory, words):
    tag, *args = q
    words = [list(w) for w in words]
    if tag == 'goto':
        return memory % 2, memory, words
    if tag == 'halt':
        return None, memory, words
    if tag == 'branch':
        return source(args[memory % 2], memory, words)
    if tag == 'load':
        return source(args[0], (memory + 1) % 3, words)
    port, tail = args
    if tag == 'push':
        words[port].insert(0, bool(memory % 2))
    elif tag in ('peek', 'pop'):
        bit = words[port][0] if words[port] else False
        memory = (memory + int(bit) + 1) % 3
        if tag == 'pop' and words[port]:
            del words[port][0]
    return source(tail, memory, words)


def compile_return(q, code):
    tag, *args = q
    start = len(code)
    code.append(None)
    if tag in ('goto', 'halt'):
        code[start] = (tag,)
    elif tag == 'branch':
        left = compile_return(args[0], code)
        right = compile_return(args[1], code)
        code[start] = ('branch', left, right)
    elif tag == 'load':
        tail = compile_return(args[0], code)
        code[start] = ('load', tail)
    else:
        tail = compile_return(args[1], code)
        code[start] = (tag, args[0], tail)
    return start


def returned(code, memory, words, saved=0, mutant=None):
    # The last two columns are private; the finite bytecode names source columns.
    cols = {i: tuple(w) for i, w in enumerate(words)}
    pc = 0
    for _ in range(len(code) + 1):
        op = code[pc]
        if op[0] == 'goto':
            saved = None if mutant == 'drop_goto' else memory % 2
            break
        if op[0] == 'halt':
            if mutant != 'stale_halt':
                saved = None
            break
        if op[0] == 'branch':
            pc = op[1] if memory % 2 == 0 else op[2]
            continue
        if op[0] == 'load':
            memory = (memory + 1) % 3
            pc = op[1]
            continue
        port = op[1]
        if op[0] == 'push':
            cols[port] = (bool(memory % 2),) + cols[port]
        else:
            word = cols[port]
            memory = (memory + (int(word[0]) if word else 0) + 1) % 3
            if op[0] == 'pop':
                cols[port] = word[1:]
        pc = op[2]
    else:
        raise AssertionError('return not reached')
    return saved, memory, [list(cols[i]) for i in range(len(cols))]


def generate(rng, depth, ports):
    if depth == 0:
        return (rng.choice(['goto', 'halt']),)
    tag = rng.choice(['push', 'peek', 'pop', 'load', 'branch', 'goto', 'halt'])
    if tag in ('goto', 'halt'):
        return (tag,)
    if tag == 'branch':
        return tag, generate(rng, depth - 1, ports), generate(rng, depth - 1, ports)
    if tag == 'load':
        return tag, generate(rng, depth - 1, ports)
    return tag, rng.randrange(ports), generate(rng, depth - 1, ports)


mutants = {}
for tag, mutant in [('goto', 'drop_goto'), ('halt', 'stale_halt')]:
    code = []
    compile_return((tag,), code)
    mutants[mutant] = returned(code, 1, [[], []], mutant=mutant) != source((tag,), 1, [[], []])
assert all(mutants.values())
cases = 0
for seed in [7, 19, 41]:
    rng = random.Random(seed)
    for _ in range(1200):
        ports = rng.randrange(1, 4)
        words = [[bool(rng.randrange(2)) for _ in range(rng.randrange(9))] for _ in range(ports)]
        memory = rng.randrange(3)
        q = generate(rng, rng.randrange(7), ports)
        code = []
        compile_return(q, code)
        label, final_memory, expected = source(q, memory, words)
        actual = returned(code, memory, words + [[], []])
        assert actual == (label, final_memory, expected + [[], []]), (seed, q, words, actual)
        cases += 1
print(json.dumps({'cases': cases, 'seeds': [7, 19, 41], 'depth': [0, 6],
                  'ports': [1, 3], 'word_lengths': [0, 8], 'failures': 0,
                  'gaveUp': 0, 'mutants': mutants,
                  'scope': 'finite statement return/branch/stack frame; no TM1 timing'}, indent=2))
