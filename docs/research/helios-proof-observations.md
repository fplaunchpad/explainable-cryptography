# Proof-valued equality observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. The proof-valued minimum-recipe branch now transfers
equality between vote worlds under the explicit smaller-observation hypothesis.
Honest proof comparisons have an unconditional provenance criterion under fresh
names. Constructed proof comparisons retain all four public arguments. The
smaller-observation hypothesis remains unproved globally, so full static
equivalence and ballot secrecy remain open.

The result uses the same sum-of-recipe-sizes interface as the
[ciphertext induction branch](helios-ciphertext-observations.md). It covers every
positive candidate count, both swaps, arbitrary valid ground candidate
substitutions and the full restricted-name policy in the final theorem.

## Honest proof provenance and the boundary case

[HonestProofEquality.lean](../../ExplainableCrypto/Helios/Symbolic/HonestProofEquality.lean)
proves exact full-E equality criteria. The parameter n encodes n + 1 candidates:

| Proof kinds | Equality criterion under `Names.Fresh` |
| --- | --- |
| Component (i, j) / component (k, l) | i = k and j = l |
| Aggregate i / aggregate k | i = k |
| Component (i, j) / aggregate k | n = 0 and i = k |
| Aggregate i / component (k, l) | n = 0 and i = k |

`component_proof_equality_iff` obtains the nonce equality from full-E proof
injectivity and recovers both indices using fresh labels.
`aggregate_proof_equality_iff` uses `honest_nonce_fold_eq_iff`: a named nonce
factor in the first voter's aggregate must occur in the other aggregate, so
freshness identifies the voter. Equal hidden message sums alone do not support
either criterion.

For a component/aggregate comparison, `component_nonce_eq_fold_iff` compares
the normal nonce factor counts. A component has one factor; an aggregate has
n + 1. Equality therefore forces n = 0. At that boundary, every nonempty fold
contains precisely the sole candidate value, and the component and aggregate
proofs for one voter coincide. The two proof fields remain different selector
recipes. Treating proof-kind tags as always distinct would be incorrect.

These results retain arbitrary valid, possibly reducible candidate values. The
nonce-fold proofs obtain the normality they need from named nonce composition;
no whole-ballot or substituted-value normality premise is imposed.

## Constructed proof comparisons

`constructed_proof_not_component` and `constructed_proof_not_aggregate` exclude
an E-equality between a publicly constructed proof and an honest proof. The
constructed nonce is a nonce-public recipe. Full-E proof injectivity would
make it equal to a restricted honest nonce or nonce fold, contradicting the
existing non-deducibility theorem. These exclusions require no board acceptance,
proof-validity or freshness premise. The key, claimed message and bound
ciphertext can be arbitrary recipe values.

[ProofObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/ProofObservationInduction.lean)
proves `constructed_proof_equality_transfer`. For two constructed proofs,
full-E equality means equality of each of the four ordered arguments: key,
nonce, claimed message and bound ciphertext. Each argument pair has total
node count strictly smaller than the two original proof recipes. The supplied
`Frame.ObservationsBelow` premise transfers these four tests.

The fourth argument is not reconstructed from the first three or omitted as
redundant. Its equality remains an explicit observation, including when it is
a reducible public ciphertext recipe. The theorem describes symbolic proof
constructor equality; it introduces no new cryptographic proof system.

## The minimum-recipe induction branch

`Historical.General.proof_form_equality_swap` covers all nine comparisons
between constructed proofs, honest component selectors and honest aggregate
selectors. Constructed/honest comparisons are false in both worlds. Honest
comparisons use the provenance criteria above, including the single-candidate
exception. Constructed/constructed comparisons use the smaller public tests.

`minimum_proof_equality_swap` derives both forms from the existing general-frame
minimum-proof-origin theorem. Its premises are:

- fresh names and arbitrary valid ground candidate substitutions;
- two minimum full-policy public recipes in the unswapped frame;
- a supplied proof-constructor value for each recipe in that frame;
- smaller public equality-test transfer at the sum of the original recipe sizes.

It concludes that equality of those same recipes transfers to the swapped
frame. It assumes no caller proof-form certificate, second-world origin or
value, nor preservation of minimum syntax. This closes the proof-valued branch
of the intended induction. It does not establish the smaller-observation
premise for all public recipes.

## Claim ledger

All names below are under `ExplainableCrypto.Helios.Symbolic`; `General`
abbreviates `Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Aggregate nonce equality determines the voter | machine-checked | `General.honest_nonce_fold_eq_iff` | Fresh labels, every positive count, full E |
| Component/aggregate nonce equality has one boundary | machine-checked | `General.component_nonce_eq_fold_iff` | Exactly n = 0 and the same voter |
| Honest proof equality follows exact provenance | machine-checked | `General.component_proof_equality_iff`, `aggregate_proof_equality_iff`, `component_aggregate_proof_equality_iff` | Actual general-frame candidate choices |
| Public constructed proofs cannot borrow honest nonces | machine-checked | `General.constructed_proof_not_component`, `constructed_proof_not_aggregate` | Nonce-public constructed nonce; arbitrary other arguments |
| Constructed proof equality transfers through all four arguments | machine-checked | `constructed_proof_equality_transfer` | Public recipes and strict smaller-observation premise |
| All proof forms transfer their equality test | machine-checked | `General.proof_form_equality_swap` | Full policy, fresh names, exact constructed or honest-selector syntax |
| The minimum proof branch needs no form certificate | machine-checked | `General.minimum_proof_equality_swap` | First-world minimum recipes and proof values, with smaller-test premise |

## Positive and negative controls

[ProofObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ProofObservationSPOT.lean)
contains eight checked controls:

- Distinct component and aggregate selector recipes are E-equal in a fresh
  one-candidate frame in both worlds. With two candidates, the same-voter
  component/aggregate values are unequal.
- Different voters' aggregate proofs remain unequal even when both voters
  abstain. Colliding nonce labels separately defeat component-proof provenance,
  demonstrating the freshness premise's role.
- A constructed proof can include an actual honest ciphertext as its fourth
  argument and still cannot equal an honest component or aggregate proof when
  its nonce recipe is public.
- A projection wrapper around a constructed bound ciphertext preserves proof
  equality. Changing only that ciphertext's plaintext from zero to one breaks
  equality while the first three proof arguments remain fixed.
- An honest selected proof value changes when the votes swap, although the
  same-index provenance tests retain their result. Pointwise proof-value
  preservation is not assumed.
- The full minimum-proof induction theorem has an inhabited diagonal-candidate
  instance with two unequal proof values and nonliteral candidate representatives.
  Identical honest assignments prove the bounded hypothesis for every size;
  this control does not assert different-vote static equivalence.

## Executable scope and validation

`ProofObservationExperiments.lean` evaluates actual component and aggregate
selectors in generated general frames. It compares their raw-normalized proof
values against an independently specified voter/candidate/kind criterion. The
generator uses one through five candidates, both swaps, valid abstention or
selected-vote assignments, both voter positions and varied candidate positions.

The mutation treating component and aggregate kinds as always distinct fails
at generated input 5, seed 1, with zero shrinks. That input is a one-candidate
same-voter component/aggregate comparison. The corrected gate passes seeds 1,
7 and 42, each with 500 configured cases, maximum size 40 and `gaveUp=0`.
It also passes a 256-input backstop and the directed inputs 160 through 799.
The first 160 inputs cover every count/kind-pair/swap/voter-pair configuration;
selected positions vary without claiming their complete Cartesian product.
The two deterministic ranges overlap and are not counted as unique inputs.

Raw equality is the executable comparison on this generated field family. The
gate is not a full-E equality decision procedure for arbitrary recipes. The
unbounded theorem and the independent binding/provenance controls establish
the stated formal scope.

Reproduce with:

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/ProofObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3470 jobs), including 20 new public theorem type/axiom
audits and three fixture definition checks. All 1192 nonempty axiom reports use
only `propext`, `Classical.choice` and `Quot.sound`; 17 additional reports are
axiom-free. There are no warnings, errors or `sorryAx`. The local log is
`tmp/variable-overlap/proof-observation-full-build.log`. The source audit checks
223 public theorem entries and selected stale claims in 14 current-status
documents; it does not replace elaboration or establish log freshness.

Trusted definitions remain E/E0, all four proof-constructor arguments, nonce
protection, public recipes, general candidates and the source's nonempty folds.
The reality oracle is Cortier–Smyth Appendix B's component and aggregate proof
construction. No equation, public operation, custom axiom or confluence
assumption changed.

The subsequent [public-key-valued branch](helios-public-key-observations.md)
derives its minimum origins and transfers equality under the same hypothesis.
Other value heads and transport of arbitrary recipe evaluations must still
establish the global smaller-observation premise. Final partial-decryption
frames and historical process matching remain open. The canonical
[task list](../../task%20list.md) retains the full static-equivalence objective.
