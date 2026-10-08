#!/usr/bin/env python3
"""Independent tree/flat-code fixtures for the existing TM1-to-TM0 translation.
Bounded tests, not Lean execution or proof of full oracle-loop compilation.
"""
import json
import random
from pathlib import Path


def expr(tag, head, mem):
    return [False, True, head, mem, head != mem, not mem][tag]


def gen(rng, depth):
    if not depth or rng.randrange(5) == 0:
        return ('halt',) if rng.randrange(2) else ('goto', rng.randrange(6))
    op = rng.choice(['move', 'write', 'load', 'branch'])
    arg = rng.choice([-1, 1]) if op == 'move' else rng.randrange(6)
    return (op, arg, gen(rng, depth-1), gen(rng, depth-1)) if op == 'branch' else (op, arg, gen(rng, depth-1))


def put(tape, head, value):
    if value:
        tape[head] = True
    else:
        tape.pop(head, None)


def source(q, mem, head, tape):
    op = q[0]
    bit = tape.get(head, False)
    if op == 'halt': return None, mem, head, tape
    if op == 'goto': return int(expr(q[1], bit, mem)), mem, head, tape
    if op == 'move': return source(q[2], mem, head+q[1], tape)
    if op == 'write':
        put(tape, head, expr(q[1], bit, mem))
        return source(q[2], mem, head, tape)
    if op == 'load': return source(q[2], expr(q[1], bit, mem), head, tape)
    return source(q[2] if expr(q[1], bit, mem) else q[3], mem, head, tape)


def bound(q):
    if q[0] in ['halt', 'goto']: return 1
    if q[0] == 'branch': return max(bound(q[2]), bound(q[3]))
    return (q[0] != 'load') + bound(q[2])


def flatten(q, code):
    if q[0] in ['halt', 'goto']: row = q
    elif q[0] == 'branch': row = (q[0], q[1], flatten(q[2], code), flatten(q[3], code))
    else: row = (q[0], q[1], flatten(q[2], code))
    code.append(row)
    return len(code)-1


def primitive(q, mem, head, tape, drop_write=False):
    code = []
    pc = flatten(q, code)
    ticks = 0
    while True:
        op, *args = code[pc]
        bit = tape.get(head, False)
        if op == 'load':
            mem = expr(args[0], bit, mem); pc = args[1]; continue
        if op == 'branch':
            pc = args[1] if expr(args[0], bit, mem) else args[2]; continue
        ticks += 1
        if op == 'halt': return (None, mem, head, tape), ticks
        if op == 'goto': return (int(expr(args[0], bit, mem)), mem, head, tape), ticks
        if op == 'move': head += args[0]
        if op == 'write' and not drop_write: put(tape, head, expr(args[0], bit, mem))
        pc = args[1]


def main():
    # Literal independently expected positive/negative witnesses precede sampling.
    q = ('write', 1, ('move', 1, ('halt',)))
    expected = (None, False, 1, {0: True})
    assert source(q, False, 0, {}) == expected
    assert primitive(q, False, 0, {}) == (expected, 3)
    assert primitive(q, False, 0, {}, True)[0] != expected
    assert primitive(('halt',), False, 0, {})[1] == 1
    assert bound(('load', 1, ('halt',))) == 1
    count = ticks = 0
    for seed in [7, 19, 41]:
        rng = random.Random(seed)
        for _ in range(1600):
            q = gen(rng, rng.randrange(8))
            tape = {i: True for i in range(-8, 9) if rng.randrange(2)}
            mem, head = bool(rng.randrange(2)), rng.randrange(-3, 4)
            expected = source(q, mem, head, tape.copy())
            actual, used = primitive(q, mem, head, tape.copy())
            assert actual == expected and 1 <= used <= bound(q)
            count += 1; ticks += used
    out = dict(cases=count, seeds=[7, 19, 41], depths=[0, 7], tape_window=[-8, 8],
               native_events=0, primitive_ticks=ticks, failures=0, gaveUp=0,
               mutants=['dropped_write', 'zero_halt_allowance'],
               scope='Independent tree and flat-code interpreters; no full oracle-loop execution.')
    Path('tmp/concrete-helios/tm1-primitive-fixtures.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
