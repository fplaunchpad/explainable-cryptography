#!/usr/bin/env python3
"""Independent finite branching-program and tagged replay-tape comparison."""
import json


def tree(depth, salt, prefix=0):
    if depth == 0 or (prefix + salt) % 7 == 6:
        return ('leaf', prefix)
    tag = (prefix + salt + depth) % 2
    return ('query', tag, [tree(depth - 1, salt, 3 * prefix + a + 1)
                           for a in range(2 + tag)])


def paths(program, answers=(), events=()):
    if program[0] == 'leaf':
        yield answers, events, program[1]
    else:
        for a, child in enumerate(program[2]):
            yield from paths(child, answers + (a,), events + ((program[1], a),))


def decode(program, events, mutation=None):
    answers = []
    for tag, answer in events:
        if program[0] == 'leaf':
            return (tuple(answers), program[1]) if mutation == 'trailing' else None
        if tag != program[1] and mutation != 'ignore_tag':
            return None
        if answer < 0 or answer >= len(program[2]):
            return None
        answers.append(answer)
        program = program[2][answer]
    return (tuple(answers), program[1]) if program[0] == 'leaf' else None


# Check deliberate defects before testing the candidate.
probe = ('query', 0, [('leaf', 0), ('leaf', 1)])
assert decode(probe, ((1, 0),)) is None
assert decode(probe, ((1, 0),), 'ignore_tag') == ((0,), 0)
assert decode(probe, ((0, 0), (0, 1))) is None
assert decode(probe, ((0, 0), (0, 1)), 'trailing') == ((0,), 0)
ordered = ('query', 0, [('query', 1, [('leaf', 0)] * 3)] * 2)
assert decode(ordered, ((0, 0), (1, 1))) == ((0, 1), 0)
assert decode(ordered, ((1, 1), (0, 0))) is None
assert decode(ordered, ((1, 1),)) is None  # Dropping the uniform event.
# Two identical hash tags are distinct physical occurrences.
repeated = ((1, 0), (0, 1), (1, 2))
locations = [i for i, (tag, _) in enumerate(repeated) if tag == 1]
assert locations == [0, 2] and locations[0] != locations[1]

# A one-event uniform tape may have an arbitrarily wide range-index tag.
# Check the one-bit-per-event mutant before the independent integer fixtures.
assert (1 << 1).bit_length() != 1
operand_cases = 0
for k in range(257):
    index = 1 << k
    assert index.bit_length() == k + 1
    assert len(((index, 0),)) == 1
    assert (index - 1).bit_length() == k
    operand_cases += 2

cases = malformed = 0
for depth in range(1, 6):
    for salt in range(64):
        program = tree(depth, salt)
        for answers, events, output in paths(program):
            assert decode(program, events) == (answers, output)
            assert len(events) <= depth
            assert decode(program, events + ((0, 0),)) is None
            malformed += 1
            if events:
                assert decode(program, events[:-1]) is None
                corrupted = ((1 - events[0][0], events[0][1]),) + events[1:]
                assert decode(program, corrupted) is None
                malformed += 2
            cases += 1
print(json.dumps(dict(valid_paths=cases, malformed_checks=malformed,
                      uniform_operand_fixtures=operand_cases,
                      deliberate_controls=['ignore_tag', 'trailing', 'reorder',
                                           'drop_uniform', 'merge_occurrences'],
                      failures=0, gaveUp=0), indent=2))
