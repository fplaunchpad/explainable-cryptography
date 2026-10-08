#!/usr/bin/env python3
"""Check original-bit archiving against indexed parsing, including rejection."""
import contextlib
import io
import itertools
import json
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    base = runpy.run_path('scripts/check-helios-record-field-step.py')


class InputTape(list):
    def __init__(self, word, archive, mutant=None):
        super().__init__(word)
        self.archive, self.mutant, self.popped = archive, mutant, 0
        try:
            self.header_end = 2*word.index(False)+1
        except ValueError:
            self.header_end = len(word)

    def pop(self, index=0):
        bit = super().pop(index)
        self.popped += 1
        if self.mutant == 'omit_header' and self.popped <= self.header_end:
            return bit
        if self.mutant == 'erase_archive':
            self.archive.clear()
        self.archive.insert(0, bit)
        return bit


def reference(word):
    try:
        width = word.index(False)
    except ValueError:
        return None, len(word)
    end = 2*width+1
    if end > len(word):
        return None, len(word)
    n = sum(int(b)*2**i for i, b in enumerate(word[width+1:end]))
    if n.bit_length() != width:
        return None, end
    if n > len(word)-end:
        return None, len(word)
    return (list(word[end:end+n]), list(word[end+n:])), end+n


def check(word, n, old_archive, mutant=None):
    archive = list(old_archive)
    tapes = [InputTape(word, archive, mutant), [], [], [], base['bits'](n), archive]
    ok, steps = base['field'](tapes)
    expected, consumed = reference(word)
    assert ok == (expected is not None)
    assert list(tapes[0]) == list(word[consumed:])
    assert tapes[5] == list(reversed(word[:consumed]))+list(old_archive)
    if expected is None:
        assert tapes[4] == base['bits'](n)
        return
    assert (tapes[3], list(tapes[0])) == expected
    flag, cost = base['decrement'](tapes)
    assert flag and tapes[4] == base['bits'](n-1)
    steps += cost+3  # record check, record finish, archived-call check
    field_len = len(tapes[3])
    while tapes[3]:
        tapes[3].pop(0)
        steps += 1
    steps += 1  # empty output halts successfully
    assert not tapes[1] and not tapes[2] and not tapes[3]
    assert tapes[5] == list(reversed(word[:consumed]))+list(old_archive)
    bound = 3*field_len.bit_length()+12+field_len*(2*field_len.bit_length()+4)+2*n.bit_length()
    assert steps <= bound


for mutant in ['omit_header', 'erase_archive']:
    try:
        check([False], 1, [True, False], mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError(f'undetected mutant: {mutant}')
cases = 0
for length in range(9):
    for word in itertools.product([False, True], repeat=length):
        for n in [1, 2, 8, 2**256]:
            for archive in [[], [False], [True, False], [False, True, True]]:
                check(word, n, archive)
                cases += 1
print(json.dumps(dict(cases=cases, failures=0, gaveUp=0, detected_mutants=2,
                     max_raw_length=8, largest_outer_counter_bits=257), indent=2))
