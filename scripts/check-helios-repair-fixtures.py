#!/usr/bin/env python3
"""Independent modular-arithmetic controls; no imports from the Lean models."""
import json
from itertools import product

P, Q, G, PK = 23, 11, 2, 8

def enc(r, m):
    return pow(G, r % Q, P), pow(G, m % Q, P) * pow(PK, r % Q, P) % P

def mul(ct, other):
    return ct[0] * other[0] % P, ct[1] * other[1] % P

def covered(r, s, vote):
    a, b = enc(r, vote), enc(s, 0)
    return [a, b, mul(a, b)]

def verify(ct, proof):
    for m, (a, b, c, z) in enumerate(proof):
        if pow(G, z, P) != a * pow(ct[0], c, P) % P:
            return False
        adjusted = ct[1] * pow(pow(G, m, P), -1, P) % P
        if pow(PK, z, P) != b * pow(adjusted, c, P) % P:
            return False
    return sum(branch[2] for branch in proof) % Q == 5

# Independently fixed valid proof for encryption E(2,1); delta=1 changes both responses.
proof = [(12, 18, 2, 3), (16, 2, 3, 10)]
assert verify(enc(2, 1), proof)
rerandomized = [(a, b, c, (z + c) % Q) for a, b, c, z in proof]
assert enc(3, 1) == (8, 12)
assert rerandomized == [(12, 18, 2, 5), (16, 2, 3, 2)]
assert verify(enc(3, 1), rerandomized)
assert not verify(enc(3, 1), proof)

counts = []
for vote in [0, 1]:
    honest_accepted = copied_aggregate_accepted = bad_event_failures = 0
    for r0, r1, s0, s1 in product(range(1, Q), repeat=4):
        a, b = covered(r0, r1, vote), covered(s0, s1, 1-vote)
        honest_ok = not any(x == y for x in b for y in a)
        honest_accepted += honest_ok
        good = set([r0, r1, (r0+r1) % Q]).isdisjoint([s0, s1, (s0+s1) % Q])
        bad_event_failures += good and not honest_ok
        attack = [a[2], (1, 1), a[2]]
        copied_aggregate_accepted += not any(x == y for x in attack for y in a)
    assert copied_aggregate_accepted == 0
    assert bad_event_failures == 0
    counts.append(dict(world=vote, cases=10000, honest_pair_accepted=honest_accepted,
                       copied_aggregate_accepted=copied_aggregate_accepted,
                       good_event_failures=bad_event_failures))
assert all(x == y for x, y in zip(covered(1, 2, 0), [(2, 8), (4, 18), (8, 6)]))
assert not set(covered(1, 2, 0)) & set(covered(4, 5, 1))
# Honest retained tally E(5,1), secret 3: share G^(3*5) and plaintext G.
ct = mul(enc(1, 0), enc(4, 1))
share = pow(ct[0], 3, P)
assert (ct, share, ct[1] * pow(share, -1, P) % P) == ((9, 9), 16, 2)
# Provenance controls: both honest ballots accepted, a fresh third accepted,
# and a copied implicit aggregate missed by component-only comparison.
a,b=covered(1,2,0),covered(4,5,1)
third=covered(6,9,0)
assert third==[(18,13),(6,9),(16,2)]
assert not set(third)&set(a+b)
cross=covered(3,4,0)
assert not set(cross[:2])&set(a[:2]+b[:2])
assert cross[0]==a[2] and set(cross)&set(a+b)
# Bob is rejected because his second zero ciphertext repeats Alice's.
# His first statement is absent from the accepted board, but can recur later.
rejected_bob=covered(4,2,1)
assert rejected_bob[1]==a[1] and rejected_bob[0] not in a
assert not set(b)&set(a) and b[0]==rejected_bob[0]
# Enumerate target-carrying valid submissions. Whenever the prefix accepted
# both honest ballots, any generated covered target is blocked. When Bob is
# rejected, count those matching submissions that actually pass retained-board
# weeding. All components/aggregates and both target plaintexts are covered.
provenance_cases=rejected_target_recurrences=0
for vote in [0,1]:
    for r0,r1,s0,s1 in product(range(1,Q),repeat=4):
        a,b=covered(r0,r1,vote),covered(s0,s1,1-vote)
        bob_ok=not set(a)&set(b)
        board=a+b if bob_ok else a
        collision=not set([r0,r1,(r0+r1)%Q]).isdisjoint([s0,s1,(s0+s1)%Q])
        for target in a+b:
            submission=[target,(1,1),target]
            accepted=not set(submission)&set(board)
            if accepted:
                assert not bob_ok and collision
                rejected_target_recurrences+=1
            provenance_cases+=1
assert provenance_cases==120000 and rejected_target_recurrences>0
# Independent three-submission shape oracle. Decisions are supplied here;
# existing cryptographic fixtures above determine their validity separately.
def retain(board, voter, decision, mutation=None):
    if decision == 'accepted' or mutation == 'append_rejected':
        return ([] if mutation == 'drop_prefix' else board) + [voter]
    return board

for mutation in ('append_rejected', 'drop_prefix'):
    board = []
    for voter, decision in enumerate(('accepted', 'accepted', 'invalidProof')):
        board = retain(board, voter, decision, mutation)
    assert board != [0, 1]
output_histories = 0
for decisions in product(('accepted', 'invalidProof', 'reusedCiphertext'), repeat=3):
    board = []
    for voter, decision in enumerate(decisions):
        board = retain(board, voter, decision)
        expected = [i for i in range(voter + 1) if decisions[i] == 'accepted']
        assert board == expected
        assert len(board) <= voter + 1
    output_histories += 1
# Literal record fields: two ciphertext pairs, three proofs with two branches.
ciphertexts = [(1, 2), (3, 4)]
proofs = [[(5, 6, 21, 22), (7, 8, 23, 24)],
          [(9, 10, 25, 26), (11, 12, 27, 28)],
          [(13, 14, 29, 30), (15, 16, 31, 32)]]
group_record = [x for ct in ciphertexts for x in ct] + [x for p in proofs for b in p for x in b[:2]]
scalar_record = [x for p in proofs for b in p for x in b[2:]]
assert group_record == list(range(1, 17))
assert scalar_record == list(range(21, 33))
assert scalar_record[:9] + [0] + scalar_record[10:] != scalar_record
# Actual multiplicative proof construction and a shared lazy oracle. This
# finite fixture tests semantics, not the distribution for all adversaries.
import random

def oracle_repair_case(seed, vote, rs, occupied):
    rng = random.Random(seed)
    neutral_key = ('ballot', G, PK, (1, 1), ((G, PK), (G, PK * G % P)))
    cache = {neutral_key: seed % Q} if occupied else {}
    requests = []
    def ask(key):
        hit = key in cache
        if not hit:
            cache[key] = rng.randrange(Q)
        requests.append((key, hit))
        return cache[key]
    def challenge(ct, proof):
        return ask(('ballot', G, PK, ct, tuple(b[:2] for b in proof)))
    def valid(ct, proof):
        c = challenge(ct, proof)
        for m, (a, b, e, z) in enumerate(proof):
            if pow(G, z, P) != a * pow(ct[0], e, P) % P:
                return False
            adjusted = ct[1] * pow(pow(G, m, P), -1, P) % P
            if pow(PK, z, P) != b * pow(adjusted, e, P) % P:
                return False
        return sum(b[2] for b in proof) % Q == c
    def prove(r, m):
        w, e, z = [rng.randrange(1, Q) for _ in range(3)]
        ct = enc(r, m)
        fake = 1 - m
        adjusted = ct[1] * pow(pow(G, fake, P), -1, P) % P
        fake_branch = (pow(G, z, P) * pow(pow(ct[0], e, P), -1, P) % P,
                       pow(PK, z, P) * pow(pow(adjusted, e, P), -1, P) % P, e, z)
        real_branch = (pow(G, w, P), pow(PK, w, P), 0, 0)
        proof = [real_branch, fake_branch] if m == 0 else [fake_branch, real_branch]
        real_c = (challenge(ct, proof) - e) % Q
        proof[m] = real_branch[:2] + (real_c, (w + real_c * r) % Q)
        assert valid(ct, proof)
        return tuple(proof)
    def ballot(r0, r1, v):
        return (enc(r0, v), enc(r1, 0)), (prove(r0, v), prove(r1, 0), prove((r0+r1)%Q, v))
    def statements(b):
        return b[0] + (mul(*b[0]),)
    def submit(board, b, expanded=True):
        if not all(valid(ct, proof) for ct, proof in zip(statements(b), b[1])):
            return 'invalidProof', board
        incoming = statements(b) if expanded else b[0]
        prior = [ct for old in board for ct in (statements(old) if expanded else old[0])]
        if set(incoming) & set(prior):
            return 'reusedCiphertext', board
        return 'accepted', board + [b]
    key_pc = pow(G, 4, P)
    key_c = ask(('key', G, PK, key_pc))
    key_proof = (key_pc, (4 + 3 * key_c) % Q)
    assert pow(G, key_proof[1], P) == key_pc * pow(PK, key_c, P) % P
    a, b = ballot(*rs[:2], vote), ballot(*rs[2:], 1-vote)
    da, board = submit([], a)
    db, board = submit(board, b)
    assert da == 'accepted'
    honest_board = list(board)
    c = ask(neutral_key)
    neutral = ((G, PK, (c-1)%Q, 1), (G, PK*G%P, 1, 1))
    attack = ((mul(*a[0]), (1, 1)), (a[1][2], neutral, a[1][2]))
    assert all(valid(ct, proof) for ct, proof in zip(statements(attack), attack[1]))
    decision, final_board = submit(board, attack)
    assert decision == 'reusedCiphertext' and final_board == honest_board
    # Changed response fails proof verification even though reuse still holds.
    changed = list(attack[1][2])
    changed[0] = changed[0][:3] + ((changed[0][3]+1)%Q,)
    malformed = attack[0], attack[1][:2] + (tuple(changed),)
    assert submit(board, malformed)[0] == 'invalidProof'
    weak_accepts = submit(board, attack, expanded=False)[0] == 'accepted'
    encrypted, shares, trustee, decoded = [], [], [], []
    for j in range(2):
        total = (1, 1)
        for old in final_board:
            total = mul(total, old[0][j])
        share = pow(total[0], 3, P)
        pc = (pow(G, 4, P), pow(total[0], 4, P))
        h = ask(('decryption', G, PK, total, share, pc))
        z = (4 + 3*h) % Q
        assert pow(G, z, P) == pc[0]*pow(PK, h, P)%P
        assert pow(total[0], z, P) == pc[1]*pow(share, h, P)%P
        plain = total[1]*pow(share, -1, P)%P
        tally = next((i for i in range(len(final_board)+1) if pow(G, i, P)==plain), None)
        expected = vote + ((1-vote) if db == 'accepted' else 0) if j == 0 else 0
        assert tally == expected
        encrypted.append(total); shares.append(share); trustee.append((pc, z)); decoded.append(tally)
    neutral_queries = [hit for key, hit in requests if key == neutral_key]
    assert neutral_queries and all(neutral_queries[1:])
    assert neutral_queries[0] == occupied
    # Pin the complete publication shape and retained board. Cryptographic
    # checks above derive its tally, key proof and both trustee proofs.
    publication = dict(parameters=(G, PK, key_proof, [0,1], [0,1,2]), fingerprint=37,
                       honest_decisions=(da, db), before=honest_board, submission=attack,
                       decision=decision, board=final_board, tally=encrypted,
                       shares=shares, trustee=trustee, decoded=decoded)
    assert len(publication['board']) == (2 if db == 'accepted' else 1)
    return weak_accepts, db

oracle_cases = weak_acceptances = 0
honest_decisions = set()
for seed in (17, 41, 103):
    rr = random.Random(seed)
    for _ in range(20):
        rs = [rr.randrange(1, Q) for _ in range(4)]
        for vote, occupied in product((0, 1), (False, True)):
            weak, honest = oracle_repair_case(seed, vote, rs, occupied)
            weak_acceptances += weak
            honest_decisions.add(honest)
            oracle_cases += 1
assert oracle_cases == 240 and weak_acceptances > 0
assert honest_decisions == {'accepted', 'reusedCiphertext'}

print(json.dumps(dict(oracle_repair_cases=oracle_cases, oracle_seeds=[17,41,103],
                     component_only_mutant_acceptances=weak_acceptances, oracle_failures=0,
                     output_histories=output_histories, results=counts, provenance_cases=provenance_cases,
                     rejected_target_recurrences=rejected_target_recurrences,
                     fresh_third_ciphertexts=third, rerandomized_ciphertext=enc(3, 1),
                     rerandomized_proof=rerandomized, honest_tally=ct,
                     decryption_share=share, gaveUp=0), indent=2))
