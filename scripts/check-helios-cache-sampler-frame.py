#!/usr/bin/env python3
"""Twelve-port caller copy/sampler fixtures, with independently calculated outputs."""
import contextlib
import io
import itertools
import json
import random
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    sampler = runpy.run_path('scripts/check-helios-prepared-scalar.py')


def execute(record, key, cache, log, tape, mutant=None):
    w = [[] for _ in range(8)] + [list(key), list(cache), list(log), list(record)]
    ticks = 0
    # Actual two-pass copy: retained operand port 11 -> input 4, scratch 0.
    while w[11]:
        w[0].insert(0, w[11].pop(0)); ticks += 1
    ticks += 1
    while w[0]:
        bit = w[0].pop(0)
        if mutant != 'erase_record': w[11].insert(0, bit)
        w[4].insert(0, bit); ticks += 1
    ticks += 1
    charge = 5*ticks+2
    ticks += 1
    if mutant == 'wrong_input': w[4] = list(w[10])
    sampled, rest, steps, cost = sampler['execute'](False, w[4], tape)
    if sampled is None: return None, w[8:], rest, ticks+steps, charge+cost
    w[:8] = sampled
    if mutant == 'erase_cache': w[9] = []
    return w, w[8:], rest, ticks+steps, charge+cost


def bits(n):
    return [bool((n >> i) & 1) for i in range(n.bit_length())]


def encoded(n):
    return [True]*n.bit_length()+[False]+bits(n)


def check(q, slack, key, cache, log, tape, mutant=None):
    record = [True]*slack+[False]+encoded(q)
    actual, retained, rest, ticks, cost = execute(record, key, cache, log, tape, mutant)
    assert retained == [key, cache, log, record]
    if q == 0:
        assert actual is None and rest == tape
        return
    width = q.bit_length()+slack
    value = sum(int(b)*2**i for i,b in enumerate(tape[:width])) % q
    assert actual == [[],bits(q),[],[],[],encoded(value),[],[],key,cache,log,record]
    assert rest == tape[width:]
    prep = slack+5*q.bit_length()+8
    div = width*(8*q.bit_length()+13)+3
    writer = 3*(q-1).bit_length()+3
    assert ticks <= 2*len(record)+2+1+prep+1+4*width+2+div+writer
    assert cost <= 5*(2*len(record)+2)+2+32*prep+5+15*width+9+32*div+32*writer


def main():
    mutants = ['erase_record','wrong_input','erase_cache']
    for mutant in mutants:
        try: check(11,0,[True,False],[False,True,True],[True,True,False],[False,True,True,False],mutant)
        except AssertionError: pass
        else: raise AssertionError('undetected '+mutant)
    count = 0
    for q, slack in itertools.product(range(17), range(3)):
        width = q.bit_length()+slack
        for coins in itertools.product((False, True), repeat=width):
            check(q,slack,[True,False],[False,True,True],[True,True,False],list(coins)+[True,False])
            count += 1
    for seed in (7,19,41):
        rng = random.Random(seed)
        for _ in range(100):
            q, slack = rng.randrange(1,4096), rng.randrange(33)
            records = [[bool(rng.getrandbits(1)) for _ in range(rng.randrange(65))] for _ in range(3)]
            tape = [bool(rng.getrandbits(1)) for _ in range(64)]
            check(q,slack,*records,tape)
    print(json.dumps({'exhaustive':count,'seeded':300,'seeds':[7,19,41],
                      'mutations_detected':mutants,'failures':0,'gaveUp':0,
                      'cost':'derived statement upper bounds; not measured exact charge'},indent=2))


if __name__ == '__main__':
    main()
