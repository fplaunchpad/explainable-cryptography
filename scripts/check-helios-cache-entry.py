#!/usr/bin/env python3
"""Whole entry execution versus independent strict indexed pair decoding."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    key = runpy.run_path('scripts/check-helios-cache-key-field.py')
field = key['field']


def machine(query, word, mutant=None):
    match, q, tapes, steps = key['machine'](query, word)
    steps += 1
    if match is None:
        return None, q, tapes, steps
    if mutant == 'skip_answer':
        return (match, []), q, tapes, steps
    ok, used = field['field'](tapes)
    steps += used+1
    if not ok or (tapes[0] and mutant != 'ignore_tail'):
        return None, q, tapes, steps
    if mutant == 'overwrite_match':
        match = True
    return (match, list(tapes[3])), q, tapes, steps


def reference(query, word):
    def natural(pos):
        width = 0
        while pos+width < len(word) and word[pos+width]:
            width += 1
        end = pos+2*width+1
        if end > len(word):
            return None
        value = sum(int(word[pos+width+1+i])*2**i for i in range(width))
        return (value, end) if value.bit_length() == width else None
    head = natural(0)
    if head is None or head[0] != 2:
        return None
    fields, pos = [], head[1]
    for _ in range(2):
        size = natural(pos)
        if size is None or size[0] > len(word)-size[1]:
            return None
        n, pos = size
        fields.append(list(word[pos:pos+n]))
        pos += n
    return (list(query) == fields[0], fields[1]) if pos == len(word) else None


def enc(n):
    return [True]*n.bit_length()+[False]+field['bits'](n)


def record(a, b):
    return enc(2)+enc(len(a))+list(a)+enc(len(b))+list(b)


def check(query, word, mutant=None):
    result, q, tapes, steps = machine(query, word, mutant)
    assert result == reference(query, word)
    assert q == list(query) and tapes[4:] == [[False, True], [True, False, False]]
    if result is not None:
        assert not tapes[0] and not tapes[1] and not tapes[2]
    L = len(word)
    assert steps <= 6*L+26+2*(L+1)*(2*L+4)+2*len(query)


for mutant, query, word in [('overwrite_match', [True], record([], [False])),
                             ('ignore_tail', [], record([], [])+[True]),
                             ('skip_answer', [], enc(2)+enc(0))]:
    try:
        check(query, word, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant: '+mutant)
queries = [w for n in range(3) for w in itertools.product([False, True], repeat=n)]
raw = 0
for n in range(13):
    for word in itertools.product([False, True], repeat=n):
        for query in queries:
            check(query, word)
            raw += 1
payloads = [w for n in range(4) for w in itertools.product([False, True], repeat=n)]
structured = 0
for a in payloads:
    for b in payloads:
        for query in queries:
            for word in [record(a,b), record(a,b)+[True], record(a,b)[:-1]]:
                check(query, word)
                structured += 1
print(json.dumps(dict(raw=raw, structured=structured, failures=0, gaveUp=0,
                     detected_mutants=3, max_raw_length=12, max_query_length=2), indent=2))
