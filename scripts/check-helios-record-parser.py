#!/usr/bin/env python3
"""Whole-record six-stack execution versus independent indexed decoding."""
import contextlib
import io
import itertools
import json
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    fixture = runpy.run_path('scripts/check-helios-archived-field.py')
base = fixture['base']


class Tape(list):
    def __init__(self, word, archive):
        super().__init__(word)
        self.archive, self.record = archive, True
    def pop(self, index=0):
        bit = super().pop(index)
        if self.record:
            self.archive.insert(0, bit)
        return bit


def count_prefix(t):
    steps = 0
    while True:
        steps += 1
        if not t[0]:
            return False, steps
        if not t[0].pop(0):
            break
        t[1].append(True)
    while True:
        steps += 1
        if not t[1]:
            if t[2] and not t[2][0]:
                return False, steps
            break
        t[1].pop(0)
        if not t[0]:
            return False, steps
        t[2].insert(0, t[0].pop(0))
    while t[2]:
        t[4].insert(0, t[2].pop(0))
        steps += 1
    return True, steps+1


def machine(word, mutant=None):
    archive = []
    source = Tape(word, archive)
    source.record = mutant != 'omit_count_header'
    t = [source, [], [], [], [], archive]
    ok, steps = count_prefix(t)
    source.record = True
    steps += 1  # count return check
    if not ok:
        return None, steps
    iterations = 0
    while t[4]:
        steps += 1  # positive count enters field routine
        ok, used = base['field'](t)
        steps += used
        if not ok:
            return None, steps+3  # record, archived call, parser return checks
        _, used = base['decrement'](t)
        steps += used+3  # record check/finish, archived call check
        while t[3]:
            t[3].pop(0)
            steps += 1
        steps += 2  # empty cleanup, parser return to loop
        iterations += 1
        if mutant == 'stop_after_one' and iterations == 1:
            break
    steps += 1  # zero-count / trailing-input check
    if source and mutant != 'ignore_trailing':
        return None, steps
    while archive:
        t[3].insert(0, archive.pop(0))
        steps += 1
    steps += 1
    return t[3], steps


def read_nat(word, pos):
    start = pos
    while pos < len(word) and word[pos]:
        pos += 1
    if pos == len(word):
        return None
    width = pos-start
    end = pos+1+width
    if end > len(word):
        return None
    value = sum(int(b)*2**i for i, b in enumerate(word[pos+1:end]))
    if value.bit_length() != width:
        return None
    return value, end


def reference(word):
    head = read_nat(word, 0)
    if head is None:
        return None
    n, pos = head
    for _ in range(n):
        head = read_nat(word, pos)
        if head is None:
            return None
        size, pos = head
        if size > len(word)-pos:
            return None
        pos += size
    return list(word) if pos == len(word) else None


def enc(n):
    payload = base['bits'](n)
    return [True]*len(payload)+[False]+payload


def check(word, mutant=None):
    out, steps = machine(word, mutant)
    assert out == reference(word)
    size = len(word)
    assert steps <= 3*size+4+(size+1)*(3*size+16+(size+1)*(2*size+4)+2*size)


for mutant, word in [('ignore_trailing', [False, True]),
                     ('stop_after_one', enc(2)+enc(0)),
                     ('omit_count_header', [False])]:
    try:
        check(word, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError(f'undetected mutant: {mutant}')
raw = 0
for size in range(13):
    for word in itertools.product([False, True], repeat=size):
        check(word)
        raw += 1
structured = 0
payloads = [[], [False], [True], [False, True], [True, False, False]]
for count in range(4):
    for fields in itertools.product(payloads, repeat=count):
        word = enc(count)+sum((enc(len(w))+w for w in fields), [])
        for variant in [word, word+[True], word[:-1]]:
            check(variant)
            structured += 1
for count in [2**12, 2**64, 2**256]:
    for rest in [[], [False], [False, False, False]]:
        check(enc(count)+rest)
        structured += 1
print(json.dumps(dict(raw_words=raw, structured_and_directed=structured,
                     failures=0, gaveUp=0, detected_mutants=3,
                     max_raw_length=12, largest_declared_count_bits=257), indent=2))
