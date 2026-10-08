# Successful symbolic proof checks

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

The successful `checkspk` branch now has a shared minimum in the simultaneous
unbounded recipe induction. Together with the existing stuck-check result,
this closes B7-C. The remaining operator obligation is successful decryption,
B7-D. Initial static equivalence and the full symbolic secrecy theorem remain
unproved. See the maintained [blueprint](helios-proof-blueprint.md).

## Checked claim and assumptions

`Historical.General.minimum_children_check_shared_of_two_way_minima` applies
to every positive candidate count, fresh historical names, valid ground
candidate substitutions and either orientation of the voting worlds. It takes
source-minimum immediate children and shared minima for strictly smaller
recipes in both directions. It returns a source-minimum public recipe whose
evaluation equals the original check in both frames.

The simultaneous induction supplies those smaller hypotheses; they are not a
new assumed static-equivalence premise. When the check succeeds, its shared
representative is the one-node public `ok`. When it is stuck, the existing
minimum theorem applies. The encoded E/E0 equations, public-name policy,
honest frame layout and candidate validity remain the trusted definitions.

## How success transfers

Minimum proof origins exhaust three cases: a public constructed proof, an
honest component-proof selector, or an honest aggregate-proof selector.

For a constructed `spk k r m d`, source success supplies four observable
equalities: `k` agrees with the supplied key, `m` agrees with a bit, `d` agrees
with the supplied ciphertext, and `d` agrees with `penc k r m`. Each comparison
fits strictly below the whole check's size. The last comparison costs exactly
the constructed proof's size. Transferring these four tests reconstructs
destination success. This result is generic over frames with the same public
policy; it requires no historical freshness or minimum-recipe premises.

For a borrowed honest proof, its key is the public handle and its bound
ciphertext is an honest indexed combination. The ciphertext argument is
minimum in the source. `minimum_honest_combination_baseEq` therefore gives
raw E0 equality with that honest combination, preserving the binding under
every substitution. Only the key comparison needs the smaller-observation
premise. Destination candidate validity supplies successful component and
aggregate checks, including abstention and reducible bit representations.

This avoids an invalid size argument: with five candidates, the aggregate
recipe costs 24 nodes and the whole check costs 38. Comparing two such
aggregate recipes costs 48, so that comparison cannot be assumed available
below the check's bound. The checked control preserves these exact numbers.

## Artifacts and retained controls

| Artifact | Public result |
| --- | --- |
| [ConstructedCheckTransport.lean](../../ExplainableCrypto/Helios/Symbolic/ConstructedCheckTransport.lean) | Four bounded comparisons transfer constructed-proof success. |
| [HonestCheckCombinations.lean](../../ExplainableCrypto/Helios/Symbolic/HonestCheckCombinations.lean) | Minimum honest ciphertexts are raw-E0-equal to indexed combinations; the exact voter fold and honest binding transfer are checked. |
| [SuccessfulCheckTransport.lean](../../ExplainableCrypto/Helios/Symbolic/SuccessfulCheckTransport.lean) | Valid honest checks, exhaustive minimum-proof success transfer and the full check operator. |
| [SuccessfulDecryptionTransport.lean](../../ExplainableCrypto/Helios/Symbolic/SuccessfulDecryptionTransport.lean) | A sufficient initial-static-equivalence criterion with successful decryption as its only remaining local transport premise. |
| [SuccessfulCheckSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SuccessfulCheckSPOT.lean) | Ten positive/negative controls, including actual minimum children, wrapped checks, three rejection defects, honest checks, one-candidate aliasing, the aggregate budget, a cross-frame counterexample and a nondegenerate diagonal criterion. |
| [SuccessfulCheckExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/SuccessfulCheckExperiments.lean) | Known-defect gate, generated constructed comparison budgets and a summary-based success oracle for generated public and honest checks. |

The three gate defects change the bound ciphertext, change the supplied key,
and use a two-one payload. Each is detected at input 0 with seed 1 and zero
shrinks. The positive campaign passes seeds 1, 7 and 42, 500 cases per seed,
size 40 and `gaveUp=0`; the deterministic backstop passes 2048 inputs. The
gate log is `tmp/variable-overlap/successful-check-gate.log` (987 jobs).
These are bounded refutation checks, not proofs of full-E decision procedures
or privacy. Kernel-checked rejection controls retain all three defects.

The independent exact-size controls and the existing
`StaticEquivalenceSPOT.raw_aggregate_observer_incomplete` preserve an important
boundary: raw normalization alone can miss a successful E0-enabled aggregate
check. The new summary harness covers its generated term shapes only.

## Remaining proof boundary

Integrated evidence: `lake build` passes 3604 jobs. The claim checker covers
766 public theorem entries and 43 current-status documents. The full log has
1732 nonempty axiom reports using only `propext`, `Classical.choice` and
`Quot.sound`, plus 20 axiom-free reports. This increment adds 22 public theorem
audits, ten SPOTs and three definition checks. Log:
`tmp/variable-overlap/successful-check-full-build.log`.

`Frame.SuccessfulDecryptionTransport` and
`Historical.General.staticEq_of_successful_decryption_transport` keep the
unproved successful-decryption instances explicit in both directions. Once
those instances are proved, this route can close initial-frame static
equivalence. It still does not discharge final transcript equivalence, the
historical process transitions and matching, or the top-level secrecy theorem.
Coverage remains six of ten top-level milestones; eleven of twelve local
operator cases are now closed. Neither count estimates remaining effort.
