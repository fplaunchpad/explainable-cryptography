# Helios replay experiment

Status: this initial finite-handle experiment and its attack controls are
machine-checked (see [results](helios-results.md)). Its restricted recipe language
is distinct from the completed historical symbolic theorem, whose B1–B10 endpoint
is `scopedVoterElection_ballot_secrecy`. The separate computational milestones are
now **3/3 complete under the revised boundary**, with external uniform-efficiency
justification and checked encoded-attacker coverage; the publication package is complete. The [scope comparison](helios-scope-comparison.md) identifies the
protocol, attacker and observation differences. No symbolic-to-computational
correspondence is claimed, and TM cleanup is outside this publication task.

This specification was written before the finite Lean implementation. It does
not specify a complete implementation of Helios or establish repair secrecy
from blocked finite attacks.

## Enquiry

Goal: explain why replay violates ballot privacy and why whole-ballot duplicate
rejection is insufficient. Candidate claim to refute: swapping two honest
voters' choices is unobservable after one corrupt voter submits a ballot.
Smallest fixture used here: Alice, Bob and Mallory, with candidates X and Y.
The formal oracles are `Replay.lean`, `Permutation.lean` and named controls
in `SPOT.lean`. The reality oracle is Cortier–Smyth, §§2.3, 3.1, 3.2.2,
5.2–5.3, with hand-derived fixtures below.

## Protocol and abstraction boundary

The source is the homomorphic Helios 2.0 description in
[Cortier–Smyth](https://publications.bensmyth.com/2012-attacking-ballot-secrecy-in-Helios/),
not Adida's 2008 mixnet. Encode X as `(1,0)`, Y as `(0,1)`, and abstention as
`(0,0)` (Figure 1). Each ballot contains two ciphertexts, two component
validity proofs and one aggregate validity proof. The aggregate checks that
at most one candidate receives a vote.

The first model uses a finite allocation of symbolic ciphertext handles: two
distinct handles per voter. Handles name encrypted components; they contain no
vote, plaintext, nonce scalar or decryption key. A separate secret environment
maps their allocations to the one-hot votes. Only the trusted tally operation
reads this environment. The adversary receives public ballots, not secrets.

Proofs are ideal certificate handles for the allocated ciphertexts and their
unordered pair. Verification compares the submitted statement with the
certificate's statement. Permuting ciphertexts and their component proofs
preserves the aggregate statement. Verification never decrypts a ciphertext.
This captures the exact replay and permutation acceptance mechanism while
abstracting the cryptographic implementation of the proofs. It is not a
formalisation of the paper's full applied-pi term algebra or a zero-knowledge
proof. In particular, it does not model re-randomisation, proof-response
malleability or neutral ciphertexts.

The finite recipe language permits copying either public honest ballot,
permuting it, submitting Mallory's fresh valid ballot with a chosen vote, and
submitting a malformed ballot for negative controls. It restricts the first
experiment, not the claimed security of Helios. Finding an accepted attack in
this restricted language gives an explicit witness; failure to find one cannot
establish security against the paper's larger adversary.

## Execution and observations

Alice and Bob are honest and publish in that order; Mallory observes both and
then submits using her own authenticated voter identity (§5.2.2). The board,
browser and tallier behave honestly. There is one election, no revoting, no
coercion, and fresh distinct symbolic allocations. Eligibility is represented
by the fixed schedule of three distinct voters, rather than an authentication
implementation.

The original policy checks proof validity. The whole-ballot policy additionally
rejects a payload identical to a preceding ballot, excluding the authenticated
sender field. Component weeding checks every submitted ciphertext against
every earlier candidate position, in addition to validity (§5.2.2).

Rejection stops the run without publishing a tally, matching Figure 4's
conditional process. The public observation contains the preceding ballots,
submitted payload, acceptance/rejection result and an optional tally. We expose
rejection as an explicit terminal outcome of this finite machine; this is not
yet a proof that its termination observations coincide with applied-pi
bisimilarity. Cryptographic partial-decryption messages are abstracted by the
trusted tally result, so the first model cannot establish secrecy of the full
cryptographic transcript.

For a fixed recipe, compare `run policy world0 recipe` and
`run policy world1 recipe`. World 0 has Alice=X and Bob=Y; world 1 has Alice=Y
and Bob=X. Mallory's chosen fresh vote is the same in both. A replay
distinguisher outputs whether the X tally is 2. A permutation distinguisher
outputs whether the X tally is 1. The witness must reach tally publication and
produce different outputs. Before Mallory's submission the public handles are
the same across worlds by construction; this idealisation is not a theorem of
computational encryption security.

## Independently derived fixtures

These totals are computed by adding the displayed plaintext vectors, before
evaluating any Lean implementation. Let `A` and `B` denote the honest ballot
payloads, `M(X)` Mallory's fresh X ballot, and `swap(A)` exchange the two
ciphertext/proof positions while retaining the aggregate proof.

| Submission | Policy | World 0 tally (X,Y) | World 1 tally (X,Y) | Outcome |
| --- | --- | --- | --- | --- |
| M(X) | all three | (2,1) | (2,1) | Accept; ordinary tally |
| A | original | (2,1) | (1,2) | Accept; replay distinguishes |
| A | whole-ballot | absent | absent | Reject duplicate payload |
| A | component | absent | absent | Reject reused ciphertext |
| swap(A) | original / whole-ballot | (1,2) | (2,1) | Accept; permutation distinguishes |
| swap(A) | component | absent | absent | Reject reused ciphertext across positions |
| malformed proof | all three | absent | absent | Reject invalid proof |

The honest tally is always `(1,1)` in the two worlds. Mallory's contribution is
Alice's vector under replay, its swapped vector under permutation, and `(1,0)`
under ordinary fresh voting. Fresh Y gives `(1,2)` in both worlds; fresh
abstention gives `(1,1)`. These provide controls against a constant tally.

## Boundary of the finite experiment

The completed symbolic theorem uses the historical term equations, arbitrary
public recipes and source transition equivalence. The computational result uses
concrete proof transcripts, random-oracle semantics, collision/replay bounds,
explicit efficiency and DDH hypotheses, and bounded tally decoding. Neither
result follows from this finite model. Their separate declarations and remaining
cross-model obligations are recorded in the [scope comparison](helios-scope-comparison.md).
The historical concrete repair's domain condition still has an
[unresolved source discrepancy](helios-repair-ambiguity.md); no exclusion of
`(1,1)` is silently added here. The selected computational repair instead has
its explicit statement-binding and expanded-weeding predicates.
