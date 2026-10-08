# Accepted-ballot values and proof provenance

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Constructor reconstruction is machine-checked for every positive candidate
count, both swaps and all valid ground candidate substitutions, including
honest abstention and arbitrary E-equivalent representatives. The
[full candidate-substitution record](helios-candidate-substitutions.md) documents
`Historical.General.accepted_ballot_constructor_recipe`, completing source
Lemma 9 with the authorised [tail-guard correction](helios-symbolic-tuple-guard.md).
Use [task list.md](../../task%20list.md) for the remaining development work.

Definition 4 permits a zero-or-one plaintext sum for honest and adversarial
voters. The sections below record the semantic interfaces and the earlier
selected-index specialization; their validation counts refer to those increments.
The general reconstruction retains public nonce recipes, literal candidate bits,
acceptance and both honest board members. Static equivalence and privacy remain
open.

## Checked claims

Declarations are in `ExplainableCrypto.Helios.Symbolic`, with the `Historical`
prefix on historical results. The first ledger records intermediate interfaces;
its aggregate alternative is excluded by the subsequent reconstruction. The
parameter `n` represents `n + 1` candidates throughout.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Aggregate ciphertext retains all nonce and plaintext factors | machine-checked | `aggregateCiphertext_values` | Arbitrary terms, common key, component E-value premises, nonempty fold |
| Aggregate validity constrains independently supplied component plaintexts | machine-checked | `ProofValid.candidate_of_ciphertexts` | Zero-or-one E-sum; component ciphertext values supplied explicitly |
| Exact component and aggregate witnesses characterize validity | machine-checked | `proofValid_iff_values` | Both directions, arbitrary reducible terms and key, every positive count |
| Acceptance retains all checks | machine-checked | `accepted_iff_values` | Same witnesses plus the existing tail guard and component weeding |
| E-equal successful proofs bind E-equal ciphertexts | machine-checked | `successful_checks_same_proof` | Both successful checks required; keys may initially differ |
| Earlier valid component proofs cannot be reused | machine-checked | `accepted_component_proof_not_reused` | Earlier ballot actually belongs to the board; both relevant checks are valid |
| Required tails have pair values | machine-checked | `ProofValid.pair_tails` | All ciphertext, component-proof and aggregate-proof positions |
| Valid ballot with tail guard has its finite tuple value | machine-checked | `ProofValid.tuple_value` | Exactly `fieldCount n` projection fields followed by bottom |
| Minimum accepted component proofs have two remaining origins | machine-checked | `Historical.minimum_accepted_component_proof_form` | Explicit spk or honest aggregate selector; both initial ballots must be on the board |
| Constructed component proof supplies a public nonce recipe | machine-checked | `Historical.accepted_component_nonce_or_aggregate` | Minimum public proof recipe, exact field E-value and bound spk value; honest aggregate branch remains |

`BallotValues` records one nonce and bit per component, component ciphertext
values, component proofs bound to their full ciphertext fields, the candidate
sum, and the aggregate proof. The aggregate uses the composed component nonces
and the summed component bits, including all repeated occurrences.
These are semantic witnesses. No theorem above makes the nonce witnesses
public recipes merely because their Lean values can be inspected.

The forward validity proof extracts successful E8/E9 checks, combines the
component ciphertexts homomorphically, and uses full-E ciphertext injectivity
to identify the aggregate nonce and plaintext. The reverse direction uses the
same field witnesses and zero-or-one sum to establish every check. No
normality premise or extra cryptographic equation is introduced.

Tuple reconstruction uses full-E projection inversion at each checked position.
A tail with a pair value equals the pair of its projections; this restricted
fact does not add a global pair-eta equation. The terminal bottom premise then
reconstructs exactly the checked finite prefix. `project_tupleWithTail_get`
separately shows why field checks alone do not constrain the terminal tail.

The historical results apply the previously checked
[minimum proof forms](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition).
If a minimum component proof were an honest component selector, proof binding
would force a reused ciphertext. Weeding excludes that case. In the constructed
case, spk injectivity identifies its nonce argument, which is public as a
subterm of the minimum public recipe. The supplied name policy remains explicit;
no freshness or arbitrary board-validity hypothesis is silently added. The
[constructor reconstruction](#constructor-reconstruction-for-the-encoded-frames)
now excludes the aggregate branch when the ballot itself has a nonce-public
recipe over the actual initial frame.

## Controls and experiment scope

`BallotValueSPOT.lean` checks independently derived literal cases:

- A one-candidate all-zero ballot is accepted. Its semantic witnesses and finite
  tuple value instantiate the general theorems. The zero-or-one condition also
  accepts the two-candidate zero-plus-zero sum.
- Exactly-one strengthening fails on zero. This is the permanent kernel control
  for the gate's minimized failure (`n = 0`, seed 1, zero shrinks).
- A two-one ballot passes both component checks but fails `ProofValid` because
  its aggregate plaintext cannot be zero or one.
- Copying a proof to a ciphertext with fresh randomness fails even though the
  vote is unchanged. Fresh honest ballots instantiate the general proof-weeding
  exclusion in both swapped worlds.
- An arbitrary terminal tail preserves the one-candidate field checks. A named
  non-bottom tail fails acceptance. A bare name refutes unconditional pair eta.
- Validity and the corrected guard permit replay; actual board weeding rejects
  it.
- Both honest ballots appear on a literal one-candidate board, after which a
  fresh all-zero adversarial ballot is accepted. Its public proof recipe has a
  minimum constructed representative. The zero plaintext excludes the honest
  aggregate branch in this concrete fixture. This control alone has that concrete scope; the general exclusion is
  proved in `GeneralAggregateExclusion.lean`.

`BallotValueExperiments.lean` enumerates every bit vector for the generated count
of one through five candidates. It compares the fold's numeric summary and
empty atom count with an independently counted number of ones, and checks the
zero-or-one predicate. It also checks every tuple field position, canonical and
named terminal tails, and proof checks with a delayed projection wrapper and
fresh-nonce rebinding. All five counts appear in the deterministic backstop;
together their vector sets contain 62 distinct vectors.

Seeds 1, 7 and 42 pass with 500 configured cases per seed, maximum size 40 and
`gaveUp=0`. All 256 deterministic inputs pass. The exactly-one negative control
fails at the smallest one-candidate all-zero vector. The gate observes raw
reduction and numeric E0 summaries; it is not a full-E equality decision
procedure or a proof of the general characterization.

Reproduce the gate with:

```sh
lake env lean ExplainableCrypto/Helios/Symbolic/BallotValueExperiments.lean
```

Validation: `lake build` passes (3421 jobs). All 28 new public theorem declarations
have type and axiom audit entries; `CandidateValues` and `BallotValues` also have
type checks. The full audit reports 932 nonempty axiom sets, each using only
`propext`, `Classical.choice` and `Quot.sound`, plus 17 axiom-free reports. The
build reports no warnings, errors or `sorryAx`.

## Constructor reconstruction for the encoded frames

`HistoricalAggregateExclusion.lean` and `AcceptedBallotReconstruction.lean`
complete the reconstruction for the earlier one-hot honest specialization.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Raw nonce factor count is bounded by a normal E-equal target | machine-checked | `EqE.compose_card_le_of_irreducible` | Irreducibility of the target is explicit; full-E raw counts are not invariant |
| A selected input contributes all its factors to a nonempty fold | machine-checked | `Historical.foldCandidates_compose_selected_lower` | Other inputs may be arbitrary reducible terms; repeated factors remain |
| Honest aggregate nonce cannot fit in a same-size normal target with other inputs | machine-checked | `Historical.nonce_fold_not_eq_small_normal` | At least two candidates; selected input E-equals the complete honest nonce fold |
| Such an aggregate-containing fold cannot be publicly deduced | machine-checked | `Historical.frame_nonce_fold_not_deducible` | Nonce-only recipe restriction and actual initial frame; all positive counts |
| Accepted component cannot use an honest aggregate proof | machine-checked | `Historical.accepted_component_not_honest_aggregate` | Public ballot recipe, acceptance, both honest board members; one-hot honest frames |
| Minimum component proof is constructed | machine-checked | `Historical.minimum_accepted_component_proof_constructed` | Minimum public proof-field recipe and exact field E-value |
| Every accepted component nonce has a public recipe | machine-checked | `Historical.accepted_component_public_nonce` | Caller need not supply a minimum whole ballot or proof recipe |
| Explicit public constructor tuple equals the accepted ballot | machine-checked | `Historical.accepted_ballot_constructor_recipe` | Both swaps and all positive counts in the encoded one-hot honest frames; literal bit witnesses satisfy the candidate sum before frame substitution |
| Selected-index specialization omits a valid source case | machine-checked | `AcceptedReconstructionSPOT.honest_abstention_scope_gap` | Accepted one-candidate all-zero ballot is not E-equal to any selected-index honest ballot |

For two or more candidates, assuming that one component borrows an honest
aggregate identifies that component's nonce with the complete honest nonce
composition. Replace that component by its E-equal named composition. The other
nonempty components add at least one factor each. An aggregate proof borrowed
from either honest ballot then has too few nonce factors, as checked against
its irreducible name-only target. A constructed aggregate proof would instead
expose a public recipe for a nonce composition containing protected names.
Nonce non-deducibility excludes that case. For one candidate, the honest
aggregate proof equals its component proof, and weeding excludes it directly.

Once component and aggregate borrowing are excluded, choose a minimum recipe
for each component proof. It is an explicit spk constructor, whose nonce
argument is public. Full-E spk injectivity identifies that argument's value
with the checked ciphertext nonce. Build each ciphertext as
`penc(var 0, nonceRecipe, const bit)` and retain the original proof-field
projections. This direct construction completes the tuple without a separate
ciphertext-factor elimination theorem.

The public conclusion exposes the nonce recipes, literal bits, proof recipes,
all publicness conditions and the final E-equality. `candidate_bits_change_variables`
transfers the constant-bit candidate condition to the recipe type, so it holds
before historical substitution. The witness is allowed to depend on the supplied
world; this is not a common-witness or static-equivalence theorem.

`AcceptedReconstructionSPOT.lean` instantiates the complete reconstruction on a
fresh two-candidate ballot after both honest ballots, for both selected positions
and both swapped worlds. It independently recovers nonce values 40/41 and the
chosen vote bits from the reconstructed ciphertexts. A second instance retains
adversarial abstention at the one-candidate boundary. A copied honest aggregate
proof passes both component checks, the corrected tail guard and weeding, but
fails `ProofValid`; the remaining aggregate check is therefore load-bearing.
Additional controls retain repeated nonce factors, reducible targets, the
one-candidate count boundary, literal private-name leakage without publicness,
and accepted honest replay when the required board members are absent.

`NonceFoldExperiments.lean` tests two through five candidates and every selected
position, with repeated honest name factors and named, composed or expanding
projection values in other positions. It compares exact raw factor counts with
an independent sum and checks count growth and exposed protected-name positions
after raw normalization. Seeds 1, 7 and 42 pass with 500 configured cases per
seed, size 40 and `gaveUp=0`; all 256 backstop inputs pass. The known-broken
full-E count bound without a normal target fails at n=0, seed 1, zero shrinks
(two factors versus a one-factor projection wrapper). These tests do not decide
full E equality. Reproduce them with:

```sh
lake env lean ExplainableCrypto/Helios/Symbolic/NonceFoldExperiments.lean
```

Validation: `lake build` passes (3426 jobs). All 37 new public theorems have type
and axiom audit entries; both tuple-construction definitions have type checks.
The audit reports 969 nonempty axiom sets using only `propext`, `Classical.choice`
and `Quot.sound`, plus 17 axiom-free reports. No warnings, errors or `sorryAx`
occur in the final build.

## Full candidate-substitution reconstruction

Appendix B.2 fixes arbitrary candidate substitutions, and Definition 4 includes
all-zero votes. `Historical.frame` takes two selected indices, so its omission
of honest abstention remains a valid scope control. `Historical.General.frame`
now accepts `CandidateSubstitution n Empty`, whose sole value constraint is the
source's zero-or-one E-sum. The selected-index frame is an exact specialization.

The full [candidate-substitution development](helios-candidate-substitutions.md)
proves component bit values, honest validity, protected-value transport, minimum
pair/ciphertext/proof origins and borrowed-aggregate exclusion for this model.
`Historical.General.accepted_ballot_constructor_recipe` returns a nonce-public
explicit tuple with a candidate substitution of literal bits before evaluation.
It covers every positive candidate count and both worlds, including arbitrary
reducible ground representatives. No minimum whole-ballot premise is required.

This completes the source Lemma 9 obligation with the authorised tail guard.
Static equivalence, process matching and ballot secrecy remain open. A
reconstruction witness may depend on its supplied world.

The later [static-transfer interfaces](helios-static-equivalence.md) preserve any
caller policy containing the honest nonces. This stronger publicness is needed
to transfer the reconstruction equality using `Frame.StaticEq`. The resulting
shared-witness and shared-plaintext theorems retain static equivalence as an
explicit hypothesis; they do not establish source Lemma 10.
