# Accepted submissions and shared numeric tallies

Status: **machine-checked**. Sequential acceptance transfers between the two
initial voting worlds without an assumed static-equivalence premise. Every
accepted submission has a shared valid literal bit vector, and the actual
partial-decryption result for each candidate is one common natural numeral.
This closes the tally obligation corresponding to source Lemma 11 within B8.
Final-frame static equivalence, including all public partial-decryption
observations, remains open. See the [blueprint](helios-proof-blueprint.md).

## Scope and chronological acceptance

[ElectionTally.lean](../../ExplainableCrypto/Helios/Symbolic/ElectionTally.lean)
defines `Frame.AcceptsSequence`: a submission must satisfy the corrected
`Accepted` predicate against the current board, then is appended before the
next submission is checked. A failed submission makes the sequence predicate
false; it is not skipped. The initial board recipes are the two honest ballot
handles. An empty adversarial suffix is allowed.

The same public recipes are interpreted in each voting world. Recipes may use
all initial observations; they are not assumed to be literal, observation-free
ballots. The source's substitutions for previously submitted handles can be
flattened into this representation, but a future process proof must establish
that connection for adaptive executions. This increment proves a statement
about accepted sequences, not the complete historical transition system.

[AcceptedSequences.lean](../../ExplainableCrypto/Helios/Symbolic/AcceptedSequences.lean)
proves generic `Frame.StaticEq.acceptsSequence_iff`, then instantiates it with
`initial_frame_staticEq` in `initial_acceptsSequence_iff`. All board and
submission recipes must be public under the same full name restriction.
Freshness and valid honest candidates are the historical theorem's inputs.

`initial_accepted_common_data` discharges the former static-equivalence premise
of shared component reconstruction. `accepted_sequence_common_data` returns
an aligned list of `SharedBallotData`. Each entry retains public nonce recipes,
literal zero/one bits, candidate validity, and an equation explaining every
submitted ciphertext component in both worlds. Both honest ballots must be on
the board when reconstruction is applied. The nonce recipes are common; their
evaluated values are not assumed equal across worlds.

## The actual tally expression

For a candidate `j`, `tallyRecipe submissions j` starts with the product of
the two honest ciphertext projections and folds multiplication over the
submitted projections. This gives at least two factors for every candidate;
no empty product or multiplication identity is introduced.

`tallyPartial` is the actual term `partialDecrypt secret tallyCiphertext`.
`tallyResult` is `dec tallyPartial tallyCiphertext`, with the whole ciphertext
binding required by E6. These definitions follow the candidate aggregates and
BB4–BB7 outputs used in Cortier–Smyth Appendix B, Lemmas 11–12 and the process
matching argument (paper pages 47–51).

[SharedTally.lean](../../ExplainableCrypto/Helios/Symbolic/SharedTally.lean)
proves the homomorphic ciphertext fold and E6 result from the aligned common
data. The two honest plaintexts exchange positions; the shared adversarial
bits stay in their original order. Addition commutativity proves the result
equality. Candidate validity and literal adversarial bits additionally give a
natural numeral bounded by the number of voters, without saturating addition
or excluding abstention.

The main statement, in namespace `Historical.General`, is:

```lean
theorem accepted_sequence_tally_numeric (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (j : Fin (n+1)) :
    ∃ k, k ≤ rs.length+2 ∧ ∀ swap : Bool,
      EqE (tallyResult ns swap left right rs j) (addNumeral k)
```

The public statement covers every positive candidate count and every finite
submission length. `accepted_sequence_tally_swap` derives equality of the two
actual results. Acceptance in the second world follows from the independent
sequence-transfer theorem; it is not silently assumed.

## Controls and evidence

[SharedTallySPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SharedTallySPOT.lean)
retains eight controls: fresh sequential acceptance in different-vote worlds;
the exact tally `0+1+1+0 = 2` with non-saturation; an empty suffix and two
abstaining honest voters yielding zero; repeated-submission rejection; honest
ballot replay rejection; recovery of the independently specified name-40 nonce
and one bit; nonliteral two-candidate tallies; and a wrong complete decryption
binding preventing an E6 match. Expected numeric results are specified
independently and checked through actual E reductions and E0 summaries.

[ElectionTallyExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ElectionTallyExperiments.lean)
first detects replay, invented-count and omitted-binding defects at input 0,
seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 cases, size 40,
`gaveUp=0`; 2048 deterministic inputs pass. The generated scope is one
candidate, zero through five fresh adversarial submissions, both assignments,
and abstention. The independent integer expectation counts the generated bits.
The finite acceptance oracle uses raw normalization on these literal fixtures
only; it is not an arbitrary full-E decision procedure. The general theorem
and the two-candidate nonliteral controls have the broader stated scope.
Gate log: `tmp/variable-overlap/election-tally-gate.log` (995 jobs).

## Remaining B8 obligation

Integrated evidence: full `lake build` passes **3612 jobs**. The claim checker
covers **799 public theorem entries** and **45 current-status documents**.
The log contains **1765 nonempty standard-only axiom reports** and **20
axiom-free reports**. This increment adds twenty public theorem audits, eight
SPOTs and ten definition checks. The main tally theorem uses only `propext`,
`Classical.choice` and `Quot.sound`. Log:
`tmp/variable-overlap/shared-tally-full-build.log`.

Equal numeric results do not prove static equivalence after public partial
decryptions are published. Those terms are not public computations from the
initial frame: their construction uses the restricted election secret. B8
still needs the actual extended-frame theorem, including every equality test
an attacker can perform using those new handles. Existing initial-frame
minimum-origin claims cannot be reused unchanged after that publication.
Historical process matching and the top-level secrecy theorem remain B9/B10.
Top-level coverage stays seven of ten milestones (70% unweighted).
