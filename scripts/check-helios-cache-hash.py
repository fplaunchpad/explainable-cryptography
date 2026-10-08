#!/usr/bin/env python3
"""Machine-backed request scheduling versus ordered map/log and entropy tapes."""
import contextlib
import io
import itertools
import json
import runpy
with contextlib.redirect_stdout(io.StringIO()):
    insertion = runpy.run_path('scripts/check-helios-cache-insert.py')
    log_append = runpy.run_path('scripts/check-helios-log-append.py')
    cache_read = runpy.run_path('scripts/check-helios-cache-read.py')
lookup = insertion['lookup']

def encode_cache(entries):
    return lookup['encode']([(key, log_append['nat'](answer)) for key, answer in entries])

def scalar_value(digits):
    value = sum(int(bit) << i for i, bit in enumerate(digits))
    assert value < 11
    return value

def driver_word(key, word, log, tape, mutant=None):
    found, _, _ = cache_read['machine'](key, word)
    requests = []
    if mutant == 'eager':
        requests.append('challenge')
    if found[0]:
        if mutant == 'log_hit':
            log = log_append['machine'](key, log)[0]
        return scalar_value(found[1]), word, log, requests
    if mutant != 'no_sample' and mutant != 'eager':
        requests.append('challenge')
    answer = tape[0] if mutant != 'no_sample' else 0
    digits = [c == '1' for c in bin(answer)[2:][::-1]] if answer else []
    scalar, _ = log_append['prefix'](digits, [])
    ok, state, _ = insertion['machine'](key, scalar, word)
    assert ok
    next_log = log_append['machine'](key, log, 'prepend' if mutant == 'prepend' else None)[0]
    return answer, state[7], next_log, requests

def check(key, entries, log, tape, mutant=None):
    old = next((a for k, a in entries if k == key), None)
    if old is not None:
        expected = old, encode_cache(entries), log_append['encode'](log), []
    else:
        expected = tape[0], encode_cache([(key, tape[0])] + entries), log_append['encode'](log + [key]), ['challenge']
    assert driver_word(key, encode_cache(entries), log_append['encode'](log), tape, mutant) == expected

for mutant in ['eager', 'log_hit', 'no_sample', 'prepend']:
    entries = [([False], 6)] if mutant in ['eager', 'log_hit'] else []
    try:
        check([False], entries, [[True]], [6, 1], mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError('undetected mutant ' + mutant)
keys = [[], [False], [True]]
answers = [0, 1, 6]
cases = 0
for n in range(3):
    for selected in itertools.permutations(keys, n):
        for values in itertools.product(answers, repeat=n):
            for key, answer, log in itertools.product(keys, answers, [[], [[True]], [[False], [True]]]):
                check(key, list(zip(selected, values)), log, [answer, 1])
                cases += 1
# Carry actual returned words through repeated requests.
sequences = 0
for initial in [[], [([], 1)], [([False], 6)]]:
    for first, second, third in itertools.product(keys, repeat=3):
        for tape in itertools.product(answers, repeat=3):
            entries = list(initial)
            word, log, position, requests = encode_cache(entries), log_append['encode']([[True]]), 0, []
            expected_log, expected_requests, expected_pos = [[True]], [], 0
            for key in [first, second, third]:
                old = next((a for k, a in entries if k == key), None)
                if old is None:
                    expected_answer = tape[expected_pos]
                    expected_pos += 1
                    entries = [(key, expected_answer)] + entries
                    expected_log.append(key)
                    expected_requests.append('challenge')
                else:
                    expected_answer = old
                answer, word, log, trace = driver_word(key, word, log, tape[position:])
                position += len(trace)
                requests += trace
                assert (answer, word, log, requests, position) == (expected_answer,
                    encode_cache(entries), log_append['encode'](expected_log), expected_requests, expected_pos)
            sequences += 1
print(json.dumps(dict(cases=cases, sequence_cases=sequences, requests_per_sequence=3,
    max_initial_entries=2, max_initial_log=2,
    detected_mutants=4, failures=0, gaveUp=0), indent=2))
