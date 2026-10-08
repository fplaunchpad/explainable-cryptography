#!/usr/bin/env python3
"""Independent finite group check for the concrete Helios nonce condition.

This enumerates encryption, component weeding and decryption modulo 23.
It does not test proof transcripts, SHA-256 or cryptographic hardness.
"""
from itertools import product
import json


def encrypt(nonce, message):
    return pow(2, nonce, 23), pow(2, message, 23) * pow(8, nonce, 23) % 23


def multiply(left, right):
    return tuple(a * b % 23 for a, b in zip(left, right))


def fresh(ballot, board):
    return all(component != old for component in ballot for prior in board for old in prior)


def main():
    results = []
    first_failure = None
    for bit in (0, 1):
        accepted_count = good_count = executed_accepted = guessed_correct = 0
        for r0, r1, s0, s1 in product(range(1, 11), repeat=4):
            first = [encrypt(r0, bit), encrypt(r1, 0)]
            second = [encrypt(s0, 1 - bit), encrypt(s1, 0)]
            attack = [multiply(*first), (1, 1)]
            accepted = fresh(second, [first]) and fresh(attack, [first, second])
            good = (all(r != s for r in (r0, r1) for s in (s0, s1))
                    and all((r0 + r1) % 11 != s for s in (s0, s1)))
            if not accepted and first_failure is None:
                first_failure = {"world": bit, "nonces": [r0, r1, s0, s1]}
            if good:
                assert accepted, (bit, r0, r1, s0, s1)
                aggregate = multiply(multiply(first[0], second[0]), attack[0])
                decrypted = aggregate[1] * pow(pow(aggregate[0], 3, 23), -1, 23) % 23
                assert decrypted == pow(2, 1 + bit, 23)
            # Execute rejection as a board-preserving transition, then tally.
            board = [first]
            if fresh(second, board):
                board.append(second)
            actual_acceptance = fresh(attack, board)
            if actual_acceptance:
                board.append(attack)
            total = (1, 1)
            for ballot in board:
                total = multiply(total, ballot[0])
            public_plaintext = total[1] * pow(pow(total[0], 3, 23), -1, 23) % 23
            guessed_correct += (public_plaintext == pow(2, 2, 23)) == bool(bit)
            executed_accepted += actual_acceptance
            accepted_count += accepted
            good_count += good
        results.append({"world": bit, "cases": 10000,
                        "all_three_accepted": accepted_count, "good": good_count,
                        "executed_attack_accepted": executed_accepted, "guess_correct": guessed_correct})
    assert [row["all_three_accepted"] for row in results] == [7200, 8100]
    assert [row["good"] for row in results] == [5200, 5200]
    assert first_failure == {"world": 0, "nonces": [1, 1, 1, 1]}
    print(json.dumps({"results": results, "unconditional_acceptance_counterexample": first_failure,
                      "good_event_failures": 0, "gaveUp": 0}, indent=2))


if __name__ == "__main__":
    main()
