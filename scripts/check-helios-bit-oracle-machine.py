#!/usr/bin/env python3
"""Independent finite-control/raw-port fixtures; no imports from Lean models."""
import itertools
import json

PROGRAM = [('hash', 0, 1, 1), ('hash', 1, 2, 2), ('hash', 0, 3, 3), ('halt',)]

def execute(word, cache, response, mutation=None):
    tape = [word, (), (), ()]
    cache = dict(cache)
    pc, cost, trace = 0, 0, []
    while pc is not None:
        command = PROGRAM[pc]
        if command[0] == 'halt':
            pc = None
            cost += 1
            continue
        _, request, destination, next_pc = command
        if mutation == 'forget_input' and pc == 2:
            request = 1
        key = tape[request]
        hit = key in cache
        if not hit:
            cache[key] = response(key)
        answer = cache[key]
        trace.append((key, answer, hit))
        cost += 1 + (0 if mutation == 'free_request' else len(key)) + len(tape[destination])
        cost += 0 if mutation == 'free_answer' else len(answer)
        tape[destination] = answer
        pc = next_pc
    return tuple(tape), cost, trace, cache

def expected(word, cache, response):
    # Evaluate the three source equations independently of the transition loop.
    saved = dict(cache)
    a = saved.setdefault(word, response(word))
    b = saved.setdefault(a, response(a))
    c = saved[word]
    return (word, a, b, c), 4+2*len(word)+2*len(a)+len(b)+len(c), saved

words = [bits for n in range(7) for bits in itertools.product((False, True), repeat=n)]
handlers = [lambda w: tuple(not b for b in w), lambda w: (True,)+w,
            lambda w: tuple(reversed(w)), lambda w: ()]
cases = 0
trace_kinds = set()
for word, response in itertools.product(words, handlers):
    for occupied in ({}, {word: (False, True)}, {word: ()}):
        result, cost, trace, cache = execute(word, occupied, response)
        want, want_cost, want_cache = expected(word, occupied, response)
        assert (result, cost, cache) == (want, want_cost, want_cache)
        assert [k for k, _, _ in trace] == [word, result[1], word]
        assert trace[-1][2]
        trace_kinds.add(tuple(hit for _, _, hit in trace))
        cases += 1
# Literal miss/miss/hit and prepopulation-dependent second query.
reply = lambda w: (True,) + w
literal = execute((False,), {}, reply)
assert literal[:3] == (((False,), (True, False), (True, True, False), (True, False)),
                       15, [((False,), (True, False), False),
                            ((True, False), (True, True, False), False),
                            ((False,), (True, False), True)])
occupied = execute((False,), {(False,): (True,)}, reply)
assert occupied[2][1][0] == (True,) and occupied[2][1][0] != literal[2][1][0]
mutants = {}
for mutant in ('forget_input', 'free_request', 'free_answer'):
    changed = execute((False,), {}, reply, mutant)
    mutants[mutant] = changed[:3] != literal[:3]
    assert mutants[mutant]
# Coin replacement must charge the erased old destination as well as its bit.
for n in range(65):
    for bit in (False, True):
        old = (False,) * n
        answer = (bit,)
        cost = 1 + len(old) + len(answer)
        assert cost == n+2 and len(answer) == 1
print(json.dumps(dict(cases=cases, word_lengths=[0,6], handlers=len(handlers),
                     trace_kinds=sorted(trace_kinds), mutants_detected=mutants,
                     coin_cases=130, failures=0, gaveUp=0), indent=2))
