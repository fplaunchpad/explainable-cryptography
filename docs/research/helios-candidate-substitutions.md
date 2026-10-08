# Candidate substitutions and accepted-ballot reconstruction

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Source Lemma 9 is complete for all valid ground
candidate substitutions, every positive candidate count and both swapped worlds,
with the authorised [tuple-tail correction](helios-symbolic-tuple-guard.md).
The main theorem is
`ExplainableCrypto.Helios.Symbolic.Historical.General.accepted_ballot_constructor_recipe`
in [GeneralAcceptedReconstruction.lean](../../ExplainableCrypto/Helios/Symbolic/GeneralAcceptedReconstruction.lean).
Static equivalence and protocol privacy remain open.
The later [static-transfer interfaces](helios-static-equivalence.md) strengthen
reconstruction to preserve the caller's full name policy and obtain a shared
witness under an explicit static-equivalence premise. Use the
[task list](../../task%20list.md) for development status.

## Candidate and frame semantics

Cortier–Smyth Definition 4 permits a sum E-equal to zero or one. Appendix B.2
fixes arbitrary candidate substitutions, so honest voters may abstain and their
terms need not be literal bits. `CandidateSubstitution n V` contains a vector
`Fin (n + 1) → Term V` and its `CandidateValues` proof. The full honest frame uses
`V = Empty`: arbitrary ground representatives satisfying that sum condition.
No separate literal-bit or exactly-one hypothesis is imposed.

`EqE.add_numeral_iff` in `NumericAdditionInversion.lean` inverts a full-E numeric
sum into numeric values of its two operands. Normalization, confluence and exact
E0 addition summaries establish this result, including reducible operands.
The zero and one cases imply `CandidateValues.component_bit` for every component
of the nonempty fold. `CandidateSubstitution.bit_representative` then supplies
a componentwise E-equal `BitCandidate`, whose literal bits still satisfy the
source candidate sum. This is a logical existence theorem, not an executable
full-E equality decider or normalization algorithm.

E0 retains AC addition, multiplication and nonce composition, with zero+zero=zero
and zero+one=one. No general zero identity, multiplication/composition unit or
one+one collapse is added. A numeric separating interpretation alone is
insufficient to recognize a candidate: `ok` has interpretation zero but is not
E-equal to a candidate bit.

Use `Historical.General.frame` for the full candidate model. It has the same
three handles as the selected-index frame: public key, first honest ballot and
second honest ballot. Names stay fixed when `swap` exchanges the two candidate
substitutions. Each ballot contains all candidate ciphertexts, all component
proofs and the aggregate proof in that order, encoded as a bottom-terminated
pair tuple. Aggregate folds start with a component and introduce no identity.
`General.selected_ballot_specialization` and `General.selected_frame_specialization`
identify the old `Historical` constructors exactly when both candidates select
one position.

`General.honest_proofs_valid` uses only the candidate sum to validate all checks.
Acceptance after the other honest ballot additionally retains distinct voters
and `Names.Fresh` to rule out nonce reuse. The source Lemma 9 reconstruction
theorem itself does not need a freshness premise.

## Protection through equivalent representations

A ground candidate can contain a projection such as `fst(pair(zero, name 20))`.
Its bit value is zero, although the discarded name can make raw syntactic
`nonceSafe` false. Consequently, raw protection of arbitrary general frames
would be an incorrect premise to assume or a false conclusion to advertise.

`General.frame_bit_representatives` gives pointwise E-equal literal-bit frame
values. Substitution congruence transports each public recipe to that frame,
whose values are syntactically protected. `General.frame_recipe_protected_value`
therefore returns an E-equal protected ground value. Individual-name and
composition-factor non-deducibility follow for every public recipe. Composed
targets may have reducible remainders; their normality is not required.

The name policy stays explicit. Lemma 9 uses `Names.nonceNames`; the privacy
frame restriction `Names.restricted` also contains the key and auxiliary names.
Changing representation while preserving each vote gives congruent recipe
values. Exchanging two different votes requires a separate static-equivalence
proof.

## Claim ledger

The short prefix `General` below means
`ExplainableCrypto.Helios.Symbolic.Historical.General`; other declarations are
in `ExplainableCrypto.Helios.Symbolic`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Candidate sum implies component bit values | machine-checked | `CandidateValues.component_bit` | Arbitrary terms, full E, every positive count |
| Candidate has a valid literal-bit representative | machine-checked | `CandidateSubstitution.bit_representative` | Componentwise E-equality; includes all-zero votes |
| Honest proof checks accept source candidates | machine-checked | `General.honest_proofs_valid` | Arbitrary ground values with the candidate sum |
| General frame has an E-equal literal-bit frame | machine-checked | `General.frame_bit_representatives` | Same vote values; both swaps |
| Public evaluation has a protected E-equal value | machine-checked | `General.frame_recipe_protected_value` | Arbitrary valid candidates; explicit public-name policy |
| Protected names and composition factors are not deducible | machine-checked | `General.frame_nonce_not_deducible`, `General.frame_nonce_factor_not_deducible` | Every public recipe; actual general frame |
| Minimum pair and ciphertext origins | machine-checked | `General.minimum_pair_and_ciphertext_origins` | Actual frame and minimum public size; strictly smaller public plaintext certificate with exact nonce/message values |
| Minimum proof syntax | machine-checked | `General.minimum_proof_form` | Explicit spk or bounded honest component/aggregate selector |
| Accepted component cannot borrow an honest aggregate | machine-checked | `General.accepted_component_not_honest_aggregate` | Nonce-public accepted ballot; both honest board members |
| Accepted component has a public nonce recipe | machine-checked | `General.accepted_component_public_nonce` | Minimum proof recipe chosen internally |
| Accepted ballot has an explicit public ciphertext tuple | machine-checked | `General.accepted_ballot_constructor_recipe` | All valid ground candidates, both swaps, all positive counts; exact conclusion below |

The general origin proofs are in `GeneralProjectionOrigins.lean`,
`GeneralMinimumOrigins.lean` and `GeneralMinimumProofs.lean`. Honest ciphertext
selectors use `CandidateValues.component_bit` to obtain constant public
plaintexts even when their raw fields contain reducible terms. The proofs do
not assert that substituted minimum recipes are irreducible.

`GeneralAcceptedProofs.lean` applies proof binding and component weeding to those
origins. `GeneralAggregateExclusion.lean` excludes the aggregate alternative.
For at least two candidates, borrowing an honest aggregate contributes its full
nonce fold to one component, exceeding the size of an honest aggregate's normal
nonce target after including the other components. A constructed aggregate would
expose protected nonce factors. For one candidate, aggregate and component
proofs coincide, and weeding excludes the borrowed proof directly.

## Exact reconstruction conclusion

Fix names, a swap, two `CandidateSubstitution n Empty` values, a `Recipe 3` and
a ground board. Assume that the recipe is public under `Names.nonceNames`, its
general-frame evaluation satisfies `Accepted`, and both actual honest ballots
belong to the board. `Accepted` retains proof validity, the corrected terminal
guard and component weeding.

The theorem returns nonce recipes indexed by `Fin (n + 1)`, literal constants
indexed by `Fin (n + 1)`, and proof recipes indexed by `Fin (n + 2)`. Its
conclusion states:

- Every returned constant is zero or one, and their sum satisfies
  `CandidateValues` in the recipe variable type before frame substitution.
- Every nonce and proof recipe is nonce-public. The complete
  `constructorBallot (var 0) nonces (fun j => const (bits j)) proofs` is also
  nonce-public.
- The original recipe and this explicit constructor tuple have E-equal values
  in the supplied general frame.

Minimum component-proof constructors supply the nonce recipes. The proof
recipes are projections of the original ballot. Reconstructing ciphertexts
from these nonces and literal bits avoids a separate ciphertext-factor
elimination argument. Neither a minimum whole-ballot recipe nor normality of
its substituted value is a premise. The existential witness may depend on the
supplied world; a common witness across worlds is not established here.

## Controls and executable scope

`GeneralCandidateSPOT.lean` checks honest abstention in both voter orders,
double abstention, nonliteral candidate acceptance, independently expected bit
representatives and the previously omitted one-candidate honest abstention.
It retains a raw-unsafe frame with E-equal protected recipe values and unbounded
name/factor non-deducibility. A public selector still extracts the expected
ciphertext, excluding an explanation based on universal stuckness. Two ones
and the numeric-interpretation shortcut are rejected for the intended reasons.

`GeneralReconstructionSPOT.lean` reconstructs a fresh adversarial ballot after
arbitrary valid honest candidates, both selected adversarial positions and both
swaps. Ciphertext injectivity independently recovers its exact nonce and bit
values. A one-candidate control has both honest voters and the adversary abstain.
A copied honest aggregate passes both component checks, the tail guard and
weeding but fails aggregate validity, uniformly for arbitrary valid honest
candidates and both swaps.

Earlier raw-normalization, factor-weight, indexed-selector, missing-minimum,
frame, publicness and board-premise controls remain checked. The old
`honest_abstention_scope_gap` remains a counterexample to the selected-index
family's source coverage; the general frame fills that omission.

| Gate | Generated scope | Deterministic backstop |
| --- | --- | --- |
| `CandidateSubstitutionExperiments.lean` | All bit vectors for generated counts one through five, with literal, projection, known-key decryption and zero-addition representatives; independent one counts against normalized numeric/atom summaries | 256 inputs |
| `GeneralCandidateExperiments.lean` | Exact fields, aggregate nonce/plaintext and tail for abstention/selection pairs and swaps | 256 inputs include all 40 count/pair-mode/swap configurations; selected positions vary but their Cartesian product is not exhausted |
| `GeneralMinimumExperiments.lean` | Pair/ciphertext/proof origins for minima in a subterm-closed finite recipe catalogue, including represented candidates | 256 inputs include 96 selector/swap/candidate-mode/fixture configurations |

Each gate passes seeds 1, 7 and 42, with 500 configured cases per seed, maximum
size 40 and `gaveUp=0`. The false numeric-interpretation shortcut fails at n=0,
seed 1, zero shrinks (`none = some 0`), with the checked regression
`GeneralCandidateSPOT.numeric_interpretation_not_candidate`. The minimum gate
uses raw-normalized catalogue values: it does not decide global full-E minima.
These campaigns are bounded refutation checks; the general claims above are
proved independently in Lean.

## Reproduce and interpret the evidence

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/CandidateSubstitutionExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/GeneralCandidateExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/GeneralMinimumExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

Validation of this candidate-substitution increment: the full build has 3441
jobs, including all controls and gates. The
76 new public theorems have both type and axiom audit entries, with another
21 definition/field type checks. The full audit contains 1045 nonempty axiom
reports, each using only `propext`, `Classical.choice` and `Quot.sound`, and
17 axiom-free reports. No warning, error or `sorryAx` occurs in the build.
The local log is `tmp/variable-overlap/general-source-reconstruction-full-build.log`;
the commands above reproduce the evidence without that generated file.
`check_helios_claims.py` checks source-level audit coverage across namespace
blocks and flags selected stale status claims. Its optional `--build-log` checks
kernel axiom reports in a supplied completed log. This smoke check neither
replaces Lean elaboration nor establishes that an old log matches current code.

Trusted semantics remain the encoded E/E0 theory, source candidate sum,
nonempty folds, recipe publicness, frame handles, proof checks, component weeding
and corrected tail guard. Source correspondence is checked against
Cortier–Smyth Definition 4 and Appendix B.2–B.3; it does not validate an actual
cryptographic implementation. No custom axiom, confluence assumption, new
cryptographic equation or public operation was introduced. Static equivalence
of honest and final partial-decryption frames, historical process matching,
ballot secrecy and computational security remain open.
