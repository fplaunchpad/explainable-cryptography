# Proof values after publication

The expanded-frame proof now classifies minimum proof values and transfers
their equality observations under smaller public tests. Explicit proof
constructors with four minimum public arguments are minimum. These are B8
dependencies; the global expanded-frame observation induction remains open.

## Claims and assumptions

`Frame.minimum_proof_origin_of_origins` extracts the existing structural
argument from the initial-frame proof. It takes actual pair origins and the
absence of successful decryption for whole minimum recipes. Both initial and
expanded frames instantiate it. The original `minimum_proof_origin` keeps its
public type. No origin or no-match assumption is silently added to an actual
frame theorem.

`expanded_projection_proof_origin` proves that a proof-valued selector chain
selects an old honest component or aggregate proof. Honest ballot positions
come from the existing tuple/field lemmas. The old election key, opaque
published partials and numeric results cannot supply new proof-valued chains.
`expanded_minimum_proof_form` therefore classifies every minimum proof-valued
recipe as an explicit four-argument constructor or one of those selectors.
`accepted_expanded_minimum_proof_form` discharges numeric results using actual
accepted public submissions and fresh names.

The mixed-case exclusions use the full public-name policy and public
submissions. `expanded_constructed_proof_not_component` rules out recovery of
an honest component nonce by any public recipe over the expanded frame.
`expanded_constructed_proof_not_aggregate` rules out recovery of a value with
the honest aggregate nonce's restricted named factor. Their proofs use the
published-frame protection invariant and need no acceptance or freshness
premise. Thus using partials, results, nested constructors or successful
destructors as nonce arguments does not circumvent these exclusions.

`expanded_minimum_spk_of_children` compares a constructed proof against an
arbitrary minimum representative. An honest alias is impossible by nonce
protection. A constructed competitor must have equivalent values in all four
arguments, so each child's minimum bound contributes to the whole bound.
The fourth bound-ciphertext argument remains explicit even for malformed
proof values; the theorem does not assume proof-check success.

`expanded_proof_form_equality_swap` has three cases. Constructed pairs use
`constructed_proof_equality_transfer`, generalized to any handle count, and
compare all four arguments under strict size bounds. Mixed pairs are false in
both worlds. Borrowed pairs are syntactic embeddings of public initial-frame
recipes, so their comparisons reuse B7 through `expanded_old_recipe_value`.
This reuse transfers observations, not minimum sizes. It retains the
one-candidate component/aggregate coincidence without introducing a separate
field-tag inequality.

`expanded_minimum_proof_equality_swap` derives the forms from source minima.
The accepted-election wrapper also discharges the numeric-result premise.
**The smaller-observation premise remains explicit.** Other expanded-value
branches and the global induction must supply its general instance.

## Controls and evidence

Eight controls in `ExpandedProofSPOT.lean` cover a minimum constructed proof
with a nested partial nonce and both honest-alias exclusions; distinct selector
syntax with equal one-candidate component/aggregate values; separated fields
with two candidates; an inhabited accepted minimum-equality step whose fourth
arguments differ; an actual borrowed minimum proof; a nonminimum projection
wrapper; exclusion of proof-valued projections from either new-handle category;
and successful structured-key E5 returning an assembled proof through a
nonminimum wrapper.

The pre-proof gate detects three mutations: omission of the fourth argument,
separation of the one-candidate fields and omission of minimum size. All fail
at input 0, seed 1, with zero shrinks. Seeds 1, 7 and 42 each pass 500 cases at
size 40 with `gaveUp=0`; 2048 deterministic inputs pass. Scope includes both
candidates and assignments, public proof nonce arguments built from partials,
results, partial constructors, keys and compositions, changed fourth bindings,
and successful E5. These are bounded checks using `normalizeRaw`, not a full-E
decision procedure. The general statements use full E.

The gate passes 1016 jobs; origin and transport targeted builds pass 927 and
928 jobs. Logs are `tmp/variable-overlap/expanded-proof-gate.log`,
`tmp/variable-overlap/expanded-proof-origins-check.log` and
`tmp/variable-overlap/expanded-proof-transport-check.log`. The eight-control build passes 1027 jobs. Full `lake build` passes
3647 jobs, with 1948 nonempty standard-only axiom reports and 20 axiom-free
reports. The claim checker covers 982 public theorem entries and 52 current-
status documents. Twenty-two new theorem audits include eight controls; two
definition checks are added. Integrated log:
`tmp/variable-overlap/expanded-proof-full-build.log`. The new modules are
`ProofMinimumTools.lean`, `ExpandedProofOrigins.lean`,
`ExpandedProofTransport.lean`, `ExpandedProofSPOT.lean` and
`ExpandedProofExperiments.lean`. The two generalized existing modules are
`GeneralMinimumProofs.lean` and `ProofObservationInduction.lean`.

The symbolic equations and public transcript definitions are unchanged. The
[blueprint](helios-proof-blueprint.md) remains at B8 and seven of ten completed
milestones (70% unweighted coverage). Other observation branches, global
shared-minimum transport, historical process matching and full symbolic
secrecy remain open.

[Expanded successful-check transport](helios-expanded-successful-checks.md) now
closes `checkspk`, retaining whole-ciphertext binding and exact honest combination
origins. The remaining local interface for all three frame presentations is
successful decryption in both directions; B8 local coverage is now 11/12.
