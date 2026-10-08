# Pair values after publication

The expanded-frame pair branch derives exact pair origins and transfers their
full equality matrix under strictly smaller public observations. Pair values
remain explicit constructors or nonempty tails of the retained honest ballots.
This is a B8 dependency; pair-root shared minimum transport and the global
expanded-frame induction remain open.

## Checked statements

`expanded_projection_pair_origin` shows that every pair-valued selector chain
is a nonempty tail of an old honest ballot. The original election key and
published partial constructors are not pairs. Numeric result slots are not
pairs, and projecting from any of these nonpair handles cannot yield a pair.
Old ballot chains reuse the existing tuple-origin and field-separation lemmas.
The theorem retains the numeric-result premise for the actual supplied frame.

`expanded_minimum_pair_observation_form` combines that chain classification
with the existing expanded minimum-pair origin theorem. Its two alternatives
are an explicit pair or a nonempty old ballot tail.
`accepted_expanded_minimum_pair_observation_form` discharges numeric results
from an accepted sequence of public submissions and fresh names.

`expanded_ballot_tail_value` gives the actual tuple suffix, including the
empty boundary. `expanded_ballot_tail_pair_value` requires the strictly
nonempty bound. `ExpandedPairObservationForm.pair_value` therefore supplies
pair-valuedness in either swapped world without destination minima,
freshness, acceptance or smaller observations.

`expanded_ballot_tail_equality_iff` reuses the initial-frame theorem through
the exact retained-handle values. Nonempty tails are equal exactly when their
voter and tail positions agree. It retains freshness and excludes empty tails;
no submission or acceptance assumption is necessary.

`constructed_pair_equality_transfer` now supports arbitrary handle counts.
It uses actual pair values in both worlds to compare the constructed fields
with the other recipe's first and second projections. Both comparisons are
strictly smaller than the original pair comparison. No universal pair eta law
is added, and pair order is preserved.

`expanded_pair_form_equality_swap` covers the whole form matrix: either
constructed side invokes the generic projection comparison; two borrowed
sides invoke retained tail identity. `expanded_minimum_pair_equality_swap`
derives forms and destination pair-valuedness from source minima. The accepted
wrapper supplies numeric results. **The smaller-observation premise remains
explicit.** These statements do not supply the global instance of that
premise or shared minimum representatives for constructed pairs.

## Independent controls

Eight statements in `ExpandedPairSPOT.lean` retain exact nonempty-tail identity,
coincident empty tails, an inhabited accepted minimum comparison of two unequal
one-node honest ballot handles, nonconstant constructed equality with nested
published fields, correct pair reconstruction and rejected truncation, invalid
eta on a published partial, an independent pair-handle fixture refuting minimum
closure from minimum children, and a successful nonminimum projection wrapper
outside the classified raw forms.

The minimum-closure counterexample is intentional: two public one-node name
children form a three-node pair, while a public one-node handle already has
that pair value. The global proof must provide a shared shorter representative
where such aliases occur. This branch does not replace that obligation with
an invalid unconditional constructor-minimum claim.

The gate detects eta on a partial, distinct empty-tail tags and unconditional
minimum-child pair closure at input 0, seed 1, zero shrinks. Seeds 1, 7 and 42
each pass 500 cases at size 40 with `gaveUp=0`; 2048 deterministic inputs pass.
The fixtures cover both voters and assignments, all five nonempty positions
of a two-candidate ballot, reconstructed tails and nested published pair
fields. Raw normalization provides bounded executable evidence, not a complete
full-E decision procedure.

## Verification and remaining work

The pre-proof gate passes 1017 jobs. The origin and transport targeted builds
pass 927 and 928 jobs. Logs:
`tmp/variable-overlap/expanded-pair-gate.log`,
`tmp/variable-overlap/expanded-pair-origins-check.log` and
`tmp/variable-overlap/expanded-pair-transport-check.log`.
The eight-control build passes 1025 jobs. Full `lake build` passes 3651 jobs,
with 1966 nonempty standard-only axiom reports and 20 axiom-free reports.
The claim checker covers 1000 public theorem entries and 53 current-status
documents. Eighteen new theorem audits include eight controls; one definition
check is added. Integrated log:
`tmp/variable-overlap/expanded-pair-full-build.log`. New modules are
`ExpandedPairOrigins.lean`, `ExpandedPairTransport.lean`,
`ExpandedPairSPOT.lean` and `ExpandedPairExperiments.lean`; the generalized
existing comparison lemma is in `PairObservationInduction.lean`.

The source equations and public frame definitions are unchanged. The
[blueprint](helios-proof-blueprint.md) remains at B8 and seven of ten completed
milestones (70% unweighted coverage). Remaining expanded-value branches,
shared minimum transport including pair-root aliases, the global observation
induction, historical process matching and full symbolic secrecy remain open.

[Expanded pair/selector transport](helios-expanded-pair-selector-minima.md) now
closes those three local roots without smaller-test premises. All local roots
and the simultaneous induction are assembled conditionally: successful
decryption/checking transport in both directions is the remaining requirement
for expanded, partial and final static equivalence.
