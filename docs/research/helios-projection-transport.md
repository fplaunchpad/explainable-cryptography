# Shared minima for successful projections

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked** for proof selectors, proof-only tails and the solved
projection cases. These results use fresh names and the actual initial frame,
cover every positive candidate count and valid ground candidate substitution,
and require no smaller-observation or static-equivalence premise. Full
initial-frame static equivalence remains open. The subsequent
[complete projection theorem](helios-complete-projections.md) closes the
ciphertext-related branches left by this module.

## Exact honest proof minima

`minimum_component_proof_selector` proves that the honest component-proof
selector at position `n+1+j` is minimum. Its size is `n+j+3`.
`minimum_aggregate_proof_selector` proves minimum size `2*n+4` for the aggregate
selector when `n ≠ 0`, meaning at least two candidates.

The proofs choose an arbitrary minimum equivalent and classify its proof
origin. A constructed proof cannot borrow the protected honest nonce. Fresh
component nonce identities determine the component index. Aggregate selectors
all have the same size, and an aggregate can equal a component only when
there is one candidate.

At one candidate, the aggregate selector at position 2 has size 4 and equals
the component selector at position 1, which is minimum of size 3.
`aggregate_selector_shared_minimum` uses that shorter component recipe in
both worlds. For larger counts it uses the already minimum aggregate recipe.
This exception is retained in the theorem and the controls.

`proof_chain_shared_minimum` covers any proof-valued fst/snd chain on an
initial public handle. It classifies the chain as a component or aggregate
selector and supplies a shared minimum. It does not assume the input chain
is minimum; the one-candidate aggregate exercises that distinction.

## Proof-only suffixes

`minimum_proof_tail` proves minimum size `k+1` for every nonempty proof-only
ballot suffix, with `n+1 ≤ k < fieldCount n`. An equivalent honest tail must
have the same position. An explicit pair representing the suffix must pay for
a minimum first proof field, its other child, and the pair root. The previously
proved selector bounds supply that lower bound, including the one-candidate
aggregate exception.

`proof_tail_shared_minimum` also includes the empty suffix at `fieldCount n`.
Nonempty proof suffixes are their own shared minima. The empty suffix instead
uses literal `bottom`, whose size is one. The raw empty-tail chain is not
claimed minimum.

## Projection cases now discharged

`SharedMinimum.projection_of_minimum_pair` uses the selected child of an
explicit minimum pair. Minimum size passes to that child, and the fst/snd
equation holds before substitution in every destination.

`projection_shared_or_pair_ciphertext` classifies every fst/snd recipe whose
child is source-minimum. It returns either a shared minimum or a source
pair/ciphertext E-value. Its proof discharges:

- Stuck projections, using minimum-parent closure.
- Projections from explicit minimum pairs, using the selected child.
- Honest component and aggregate proof fields.
- Nonempty proof-only suffixes and the empty suffix.

The branches left open by that proof select honest ciphertext fields or
retain tails with ciphertext fields still present. The public disjunction
states the broader pair/ciphertext output classes; it does not assert that
such a value rules out a shared minimum. `proof_projection_shared_minimum`
extracts the complete shared-minimum result for proof-valued projections by
excluding those two other value classes.

Freshness and the full name restriction remain explicit. No destination
minimum-size judgment, raw-normality assumption or preservation of smaller
equality tests is supplied by the caller. The subsequent complete projection theorem closes all local projections;
the other local root cases remain open.

## Controls and reproducible evidence

Seven public controls retain:

- Exact two-candidate component and aggregate minimum sizes 4, 5 and 6.
- The one-candidate nonminimum aggregate and its actual shorter public equal
  recipe.
- A shared minimum for that nonminimum chain, plus minimum size for its
  component selector and final nonempty proof tail.
- Colliding nonces making a later component selector nonminimum, despite valid
  vote substitutions.
- Both selectors of an explicit minimum pair, with distinct selected names.
- All proof-only suffixes in the two-candidate fixture and the nonminimum
  empty-tail boundary with a shared bottom representative.
- A proof-valued successful projection from a minimum honest suffix under the
  actual different-vote swap.

The Plausible gate first detects the one-candidate aggregate defect at input 0,
seed 1, zero shrinks. The positive campaign varies one through five candidate
counts and public names in both swapped frames. It checks canonical aggregate
values, selector-size budgets, explicit pair selection, empty tails, and
canonical first-field values and size budgets for every proof-only suffix.
Seeds 1, 7 and 42 pass 500 configured cases each, size 40, `gaveUp=0`; all 2048
backstop inputs pass. The tests compare raw normal forms on this fixture family;
they do not decide arbitrary E equality or prove absence of smaller recipes.
The unbounded minimum claims come from the Lean origin and size arguments.

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/ProjectionTransportExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/projection-transport-full-build.log
```

The five new modules are `HonestProofMinima`, `HonestProofTailMinima`,
`ProjectionMinimumTransport`, `ProjectionTransportExperiments` and
`ProjectionTransportSPOT`. The audit checks eighteen public theorem types and
axiom sets, including seven controls. The full build passes (3542 jobs), with
1502 nonempty axiom sets using only `propext`, `Classical.choice` and `Quot.sound`,
and 17 axiom-free reports. No warnings, errors or `sorryAx` occur. The claims
checker covers 533 public theorem entries and 29 current-status documents.
Build evidence is in the
[results ledger](helios-results.md#successful-projection-transport-enquiry).

Trusted definitions remain the term signature, E/E0, public names and handles,
actual candidate frames, tuple layout, full-E origin/injectivity theorems,
node count and minimum recipes. No cryptographic equation, public operation,
custom axiom or confluence premise changed. See the
[local-root record](helios-local-root-transport.md) and
[observation assembly](helios-observation-assembly.md). Other remaining root transport, final public partial decryptions and process
privacy remain open in the task list.
