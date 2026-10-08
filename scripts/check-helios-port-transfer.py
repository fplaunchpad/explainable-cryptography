#!/usr/bin/env python3
"""Independent finite-state transfer oracle; no Lean imports or generated values."""
import itertools
import json


def execute(tapes, roles, saved, local=None, mutation=None, consume=False):
    tapes = {k: list(v) for k, v in tapes.items()}
    src, dst, scratch = roles
    phase = 'copy' if mutation == 'append' else 'clear'
    steps = 0
    while phase is not None:
        steps += 1
        if phase == 'done':
            if consume and tapes[src]:
                local = tapes[src].pop(0)
            else:
                local = None
                phase = None
            continue
        k = dst if phase == 'clear' else src if phase == 'copy' else scratch
        local = tapes[k].pop(0) if tapes[k] else None
        if phase == 'clear':
            if local is None:
                phase = 'copy'
        elif phase == 'copy':
            if local is None:
                phase = 'done' if mutation == 'one_pass' else 'restore'
            else:
                tapes[scratch].insert(0, local)
        elif phase == 'restore':
            if local is None:
                phase = 'done'
            else:
                if mutation != 'erase_source':
                    tapes[src].insert(0, local)
                tapes[dst].insert(0, local)
        else:
            raise AssertionError(phase)
        assert steps < 100
    return {k: tuple(v) for k, v in tapes.items()}, saved, local, steps

words = [w for n in range(6) for w in itertools.product((False, True), repeat=n)]
base_cases = frame_cases = request_cases = consuming_cases = 0
for word, old in itertools.product(words, repeat=2):
    for local in (None, False, True):
        out, saved, final_local, used = execute({0: word, 1: old, 2: ()}, (0,1,2), 7, local)
        assert out == {0: word, 1: word, 2: ()}
        assert saved == 7 and final_local is None
        assert used == len(old)+2*len(word)+4
        base_cases += 1
        moved, kept, final_local, used = execute({0:word, 1:old, 2:()}, (0,1,2), 7, local, consume=True)
        assert moved == {0:(), 1:word, 2:()} and kept == 7 and final_local is None
        assert used == len(old)+3*len(word)+4
        consuming_cases += 1
    for destination, saved in itertools.product(range(3), (0,1,6)):
        original = {0: (True,), 1: (False,True), 2: (True,False,False)}
        original[destination] = old
        tapes = {**original, 3: word, 4: ()}
        result, kept, final_local, used = execute(tapes, (3,destination,4), saved, consume=True)
        expected = {**original, destination: word, 3: (), 4: ()}
        assert result == expected and kept == saved and final_local is None
        assert used <= len(old)+3*len(word)+4
        frame_cases += 1
        original[destination] = word
        issued, kept, _, before = execute({**original, 3:old, 4:()}, (destination,3,4), saved)
        assert issued == {**original, 3:word, 4:()} and kept == saved
        assert before == len(old)+2*len(word)+4
        request_cases += 1
literal = {0: (True,False), 1: (True,), 2: ()}
want = execute(literal, (0,1,2), 6)
assert want == ({0:(True,False), 1:(True,False), 2:()}, 6, None, 9)
mutants = {}
for mutation in ('append', 'one_pass', 'erase_source'):
    mutants[mutation] = execute(literal, (0,1,2), 6, mutation=mutation)[0] != want[0]
    assert mutants[mutation]
dirty = execute({0:(True,False),1:(True,),2:(True,)}, (0,1,2), 6)
assert dirty[0] != want[0]
# Successive native calls start and finish with empty private workspace.
# Alias request and destination to expose incorrect ordering at the handoff.
combined_cases = 0
for word, answer in itertools.product(words, repeat=2):
    # Clear initial native query port is the invariant used by the composed bound.
    issued, kept, _, before = execute({0:word,1:(),2:()}, (0,1,2), 6)
    assert issued[1] == word and issued[0] == word
    delivered = {**issued, 1:answer}
    finished, kept, _, after = execute(delivered, (1,0,2), 6, consume=True)
    assert finished == {0:answer,1:(),2:()} and kept == 6
    assert before+1+after <= 9*(1+len(word)+len(word)+len(answer))
    combined_cases += 1
coin_cases = 0
for old, bit in itertools.product(words, (False, True)):
    finished, kept, _, after = execute({0:old,1:(bit,),2:()}, (1,0,2), 6, consume=True)
    assert finished == {0:(bit,),1:(),2:()} and kept == 6
    assert 1+after <= 9*(2+len(old))
    coin_cases += 1
# An uncleared ten-bit native port takes nine ticks without completing even its clear phase.
assert 10+2*0+4 > 9*(1+0+0+0)
print(json.dumps(dict(base_cases=base_cases, framed_cases=frame_cases, consuming_cases=consuming_cases,
                     request_cases=request_cases, combined_cases=combined_cases, coin_cases=coin_cases, word_lengths=[0,5],
                     mutants_detected=mutants, dirty_scratch_detected=True,
                     failures=0, gaveUp=0), indent=2))
