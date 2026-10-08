#!/usr/bin/env python3
"""Independent native-word/handler fixtures through the two physical transfer interpreters.
Response stack projection is direct here; this is not a TM1 call-loop timing test.
"""
import contextlib
import io
import json
import random
import runpy

with contextlib.redirect_stdout(io.StringIO()):
    export = runpy.run_path('scripts/check-helios-oracle-tape-output.py')['export']
    load = runpy.run_path('scripts/check-helios-oracle-tape-input.py')['load']


def native_word(cells):
    result = []
    for bit in cells:
        if bit is None:
            break
        result.append(bit)
    return tuple(result)


def handler(word, cache, log):
    hit = word in cache
    if not hit:
        cache[word] = (True,) + tuple(not bit for bit in word[:5])
    log.append((word, hit))
    return cache[word]


cases, seeds = 0, [7, 19, 41]
for seed in seeds:
    rng = random.Random(seed)
    for _ in range(960):
        word = tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(9)))
        occupied = {word: tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(9)))} if rng.randrange(2) else {}
        expected_words = [word, (), (), ()]
        expected_cache, expected_log = dict(occupied), []
        actual_words = list(expected_words)
        actual_cache, actual_log = dict(occupied), []
        previous = tuple(bool(rng.randrange(2)) for _ in range(rng.randrange(9)))
        for source, destination in [(0, 1), (1, 2), (0, 3)]:
            expected_answer = handler(expected_words[source], expected_cache, expected_log)
            expected_words[destination] = expected_answer
            words = actual_words + [actual_words[source], ()]
            query, wh, qh, lo, _, frame = export(words, 4, previous=previous)
            assert wh == 0 and qh == lo and frame
            assert native_word(query + (None, True)) == query
            answer = handler(native_word(query), actual_cache, actual_log)
            loaded, wh, ah, _, retained = load(words, 4, answer)
            assert wh == ah == 0 and retained == answer
            assert loaded[:4] == tuple(actual_words) and loaded[4:] == (answer, ())
            actual_words[destination] = loaded[4]
            previous = query
        assert actual_words == expected_words
        assert actual_cache == expected_cache and actual_log == expected_log
        assert actual_log[-1][1]  # The last H(x) uses the original cache entry.
        cases += 1
prefix_cases = 0
rng = random.Random(41)
for _ in range(2000):
    cells = [rng.choice((None, False, True)) for _ in range(rng.randrange(17))]
    stop = cells.index(None) if None in cells else len(cells)
    assert native_word(cells) == tuple(cells[:stop])
    assert native_word(cells + [None] * rng.randrange(8)) == native_word(cells)
    prefix_cases += 1
assert native_word([True, None, False]) != tuple(b for b in [True, None, False] if b is not None)
print(json.dumps(dict(cases=cases, seeds=seeds, calls_per_case=3, lengths=[0, 8],
                     prefix_cases=prefix_cases, failures=0, gaveUp=0,
                     mutants={'skip_blank': True},
                     scope='native decoding, adaptive cache/log and physical region composition; no TM1 loop timing'), indent=2))
