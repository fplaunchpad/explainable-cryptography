# Full Named visible actions and election classification

Current frontier: [input/bound-output invariant preservation](helios-source-visible-invariant.md)
now retains full target classes and fresh output handles with election visible
determinism. A checked counterexample shows the body invariant alone does not
retain channel restriction. Public-policy/label alignment, arbitrary related
process action construction and final secrecy remain open. Earlier boundary
statements below record their historical checkpoint.

Current frontier: [the full target invariant](helios-source-target-invariant.md)
now preserves all canonical realizations through arbitrary actual internal
source actions and finite internal traces, with fresh value refresh and exact
next-phase frame/domain alignment. Visible closure, arbitrary-representative
action construction and final secrecy remain open. Earlier boundary statements
below record their historical checkpoint.

Current frontier: [structural opening comparison and fresh internal matching](helios-source-opening-comparison.md)
now cover every Structural rule and actual internal reductions from canonical
structural representatives, including checks. Targets have coherent full
interpretations and one-step opposite-world matches with StaticEq. Relation/
target closure and final secrecy remain open. Earlier boundary statements below
record their historical checkpoint.

Current witness frontier: [fresh canonical openings](helios-source-openings.md)
now construct actual source paths and full frame/body permutation witnesses.
Comparison through arbitrary structural/action paths and final secrecy remain
open; earlier witness-boundary statements below describe their checkpoint.

Current guard frontier: [equational recovery](helios-source-guard-retractions.md)
now supplies a sufficient truth-preservation condition that handles unused-field
collisions. Coherent Named witnesses and final secrecy remain open. Earlier
guard-boundary statements below describe their checkpoint.

Current internal frontier: [exact conditional location and arbitrary non-check
matching](helios-source-conditional-location.md) are now proved. Check-phase
truth correspondence, required target invariants and final secrecy remain open.
Earlier internal-boundary statements below describe their checkpoint.

Current internal frontier: [general Named communication and actual election
matching](helios-source-communication.md) are now checked without injectivity.
Arbitrary Named conditional correspondence, required target presentation/relation
invariants and final secrecy remain open. Earlier open internal statements below
describe their checkpoint; B9/B10 are still incomplete.

Status: **machine-checked** B9 increment. Every actual Named free/bound output
step transports a complete `Named.Interprets` witness to evaluated visible
behavior and the full target interpretation. B9/B10 remain incomplete at 8/10
unweighted milestones (80%).

## Visible action theorem

[SourceNamedVisibleInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceNamedVisibleInterpretation.lean)
proves `Named.FreeStep.interprets` and `Named.BoundOutput.interprets` for all
current constructors and arbitrary structural paths. The proof factors the
actual action beneath a common name prefix, transports the full interpretation
across its actual structural paths, maps the Extended action and reconstructs
the complete target. The prefix fixes the full free label, including every
input proof field; bound-output scope fixes the channel. Both visible source
rules already map forward under arbitrary atom/channel assignments. Thus these
statements have **no injectivity or faithful-assignment premise**.

The free-input result preserves the exact evaluated input recipe. A free output
retains a complete emitted message E-equal to the old handle value. A bound
output extends the original environment by the actual emitted message and
retains the entire target body. It does not replace that value with a tally,
redaction or chosen representative.

[SourceNamedCanonicalVisible](../../ExplainableCrypto/Helios/Symbolic/SourceNamedCanonicalVisible.lean)
applies these results to actual canonical states. `canonical_input_scoped`
retains the original frame and its structural `RepresentsFrame` witness at the
raw target. The public-recipe premise is explicit. The stronger
`common_fresh_canonical_input` chooses common fresh state representatives,
preserves two-world frame observations, keeps the original recipe/channel and
raw target unchanged, and supplies an actual scoped input with target
interpretation and frame presentation. This discharges the previously separate
visible connection from a canonical Named representative to its factored body.

`canonical_output_scoped` retains the actual emitted message, the exact extended
frame and the raw target interpretation before and after `outputHandle` renaming.
It does not assert a structural presentation for that new frame. Such a claim
requires evidence beyond the target's interpretation.

## Actual election behavior

[SourceNamedElectionVisible](../../ExplainableCrypto/Helios/Symbolic/SourceNamedElectionVisible.lean)
classifies inputs and bound outputs from any raw source process interpreting an
in-range election body, assuming the action channel is public. Its canonical
corollaries derive channel publicness from the actual Named action.

An input comes from the input phase on the next voter channel, and its target
interprets the complete pending guard plus untouched threads. It does not
assert recipe publicness under the original fixed policy. An output is exactly
one of the first ballot, second ballot, partial-decryption tuple or result tuple
publications. The result retains the complete payload, literal publication
stage, `Process.Step`, exact next-frame capture (with its handle type), and
full continuation under the extended environment. These are general source
results; their hypotheses require range/public-channel conditions rather than
assuming that the target was already canonical.

## Internal transport and counterexamples

[SourceFiniteFaithfulAssignments](../../ExplainableCrypto/Helios/Symbolic/SourceFiniteFaithfulAssignments.lean)
defines `NameAssignment.FaithfulOn`: the assigned sorted names are injective on
a specified finite set. Equal numerals in the two different sorts remain
separate. Mathlib's `Equiv.Perm.exists_extending_pair` supplies separate global
permutations agreeing with the assignment on that set. Their values elsewhere
may change.

`Extended.reduction_mapAssignments_iff` transports and reflects an actual
Extended internal reduction when the assignment is faithful on the union of
both endpoint supports. Intermediate derivation names need no additional
premise: the genuine permutations transport the whole derivation, and support
agreement identifies the endpoints. `Reduction.interprets_faithful` then gives
an actual evaluated Tau and full mapped target interpretation.

This sufficient internal condition is not yet discharged for arbitrary Named
paths. The retained alpha control maps bound 50 back to its original exported
40 while fixing unused outside names. Global injectivity would exclude that
legitimate interpretation. A second counterexample rewrites `{50/x}` into
`{fst(pair(50,40))/x}` under the same binder. Full E permits this actual rewrite
and the old environment still interprets it. However, fixing the outside 40
and exporting 40 forces the assignment of 50 to 40, violating even injectivity
on that expanded syntactic support. A fixed old environment is therefore too
strong a requirement for the proposed internal witness construction. Coherent
fresh canonical representatives or a stronger semantic argument are required.
The unconditional internal theorem remains unproved.

## Controls and evidence

[SourceNamedVisibleSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceNamedVisibleSPOT.lean)
contains twenty-two public kernel controls: an actual alpha-closed input with
unchanged old literal; rejection of its old policy; full key and output
interpretation; real voter input classification and frame presentation; full
SPK output capture; stopped/rejected output and input exclusion; exact first
publication classification with an actual existence witness; sorted finite
faithfulness and permutation extension; global-injectivity and dead-field
counterexamples; and retained guard/channel collision controls.

Integrated verification: `lake build` passes **3984 jobs**. The log reports
**3942** nonempty standard-only and **74** axiom-free results. The claim audit
covers **3030** public theorem entries and **112** current-status documents.
All seven changed Lean sources have current oleans; **1434** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **43** theorem audits,
including **22** public kernel controls, and checks the finite-faithfulness
definition. The targeted control build passes **1337 jobs**.
Build log: `tmp/variable-overlap/source-named-visible-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-named-visible-verification.txt`.

The gate combines general proofs with independently specified literal kernel
controls. No new randomized cryptographic campaign is claimed. Existing
experiments may replay in the full build. Cortier–Smyth Figures 2–4 and the
existing source rules supply the reality reference. Full E/E0, structured-key
E5, full-ciphertext E6, SPK fourth fields and explicit public observations are
unchanged. No source rule or custom axiom is added.

Remaining obligations: general Named internal correspondence; required target
presentation and relation invariants through arbitrary source actions; and the
final source weak labelled bisimilarity/symbolic secrecy theorem. A conditional
internal transport result is not the secrecy theorem. Independent frame
compatibility and Named static transitivity remain closed. Maintain the
[blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md) and
existing B9/B10 item in [task list.md](../../task%20list.md).
