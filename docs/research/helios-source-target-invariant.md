# Full target invariant and repeated internal actions

Current follow-up: [structural action openings](helios-source-structural-openings.md)
retain actual binder-structural endpoint paths and characterize Named structure
by jointly fresh structural openings. General reachable reconstruction and
final secrecy remain open.

Current frontier: [joint internal closure](helios-source-joint-internal.md) now
retains the actual restricted canonical state through raw internal steps and
finite internal traces. Joint visible closure, the source-action converse and
final secrecy remain open. Earlier boundary statements below describe their
historical checkpoint.

Current frontier: [input/bound-output invariant preservation](helios-source-visible-invariant.md)
now retains full target classes and fresh output handles with election visible
determinism. A checked counterexample shows the body invariant alone does not
retain channel restriction. Public-policy/label alignment, arbitrary related
process action construction and final secrecy remain open. Earlier boundary
statements below record their historical checkpoint.

Status: **machine-checked** B9 increment. Full canonical realization classes
are preserved by actual internal reductions with deterministic canonical targets.
The opening invariant can be refreshed and reused on raw targets. Every finite
sequence of actual Named internal actions from a reached phase invariant has a
corresponding stage-internal sequence and retains the invariant at its target.
This is source-to-stage preservation; B9/B10 remain incomplete at 8/10
unweighted milestones (80%). Final symbolic secrecy is still unproved.

## Backward realization and complete target classes

[SourceBackwardRealization](../../ExplainableCrypto/Helios/Symbolic/SourceBackwardRealization.lean)
proves `Extended.Reduction.realizes_backward`. For any full target realization
under a ground environment, it constructs a full source realization in that
same environment and an actual Tau whose target is EvalEq to the chosen target
body. EvalEq is the interpretation's existing parallel/full-E equivalence;
the actual Tau relation has not been enlarged. The proof covers communication,
both conditional rules, parallel contexts, existential variable scopes and
arbitrary structural pre/post paths. `has_realization_iff` shows that an actual
reduction preserves exactly which environments admit a full realization.

[SourceRealizationTargetClosure](../../ExplainableCrypto/Helios/Symbolic/SourceRealizationTargetClosure.lean)
proves `Reduction.sameRealizations_frame_target`. Its source premise is equality
of all full realizations with `frameProcess φ p`, not merely one realization
in `φ.value`. Its determinism premise says every actual Tau from `p` has a target
EvalEq to `q`. The conclusion is equality of all target realizations with
`frameProcess φ q`, under every environment and complete body. Backward
realization supplies the forward implication and preserves all active equations;
forward realization and determinism supply the reverse implication. The frame's
full values are retained. No source Structural presentation is inferred from
this semantic equality. A quiet canonical body excludes source reductions from
this complete class, using its nonempty canonical realization.

## Paired actions and refreshing values

[SourcePairedOpeningReduction](../../ExplainableCrypto/Helios/Symbolic/SourcePairedOpeningReduction.lean)
constructs one faithful assignment and the same allocation for both endpoints
of an actual Extended action under a pure name prefix. `Opens.prefix_reduction`
retains an actual Extended reduction between the two opened endpoints.
`Named.Reduction.opening_step` derives finite avoidance from an arbitrary actual
Named action. It transports the chosen source opening to a paired Extended
action and reconstructs an opening of the unchanged raw target. Full-realization
comparisons connect both ends; any extra finite avoidance set is retained.
This strengthens the earlier target-interpretation-only result.

[SourceOpeningValuePermutations](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningValuePermutations.lean)
defines sorted `NameAssignment.mapValues`: it permutes assigned values without
renaming source binder keys. `Opens.mapValues` retains the full body and maps
the allocation list under actual bijections. `mapValues_literal` keeps literal
outer assignment when free source names are fixed. `Opens.refresh` starts with
allocations disjoint from the source's free names and constructs value
permutations avoiding any new finite set while fixing all free source names.
The existing common-fresh-prefix construction supplies these permutations.
Distinctness and all full payload/guard fields remain in the opening witness.
The external-freshness premise excludes a captured free literal.

## An invariant that survives raw internal targets

[SourceCanonicalOpeningInvariant](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalOpeningInvariant.lean)
defines `Named.HasCanonicalOpening a φ p`. It records an externally fresh literal
opening of `a` whose Extended body has exactly the same full realizations as
`frameProcess φ p` under two witnessed name permutations. Both implications
quantify every ground environment and complete Agent body. It is proof
instrumentation; it does not add a source transition or replace the final
protocol equivalence relation.

The invariant can avoid any further finite set by refreshing and composing its
coordinate permutations. It is stable under every actual Structural rule.
Canonical restricted states have it, as do their structural representatives.
It is nonvacuous: it supplies a full raw interpretation in a coherently mapped
frame/body environment. The permutations need not fix every potential public
recipe name; public-policy alignment remains a separate obligation.

[SourceCanonicalOpeningInternal](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalOpeningInternal.lean)
proves `HasCanonicalOpening.tau`, deriving an actual Tau in original canonical
coordinates from an arbitrary actual Named reduction. No canonical Structural
presentation of its source is assumed. `HasCanonicalOpening.internal` preserves
the invariant when all canonical Tau outcomes agree with the chosen successor
modulo EvalEq. The proof uses a fresh paired opening of the actual action, full
Extended target-class closure and the target's structural opening comparison.
The resulting raw target can be refreshed for another action.

This is closure under consuming an existing actual source action. It does not
construct a source action in an arbitrary invariant representative from a
canonical Tau. That converse, or a stronger reachable/admissible relation with
such a converse, remains necessary for final bisimulation.

## Exact election phases and finite internal sequences

[SourceInternalFrameIdentity](../../ExplainableCrypto/Helios/Symbolic/SourceInternalFrameIdentity.lean)
proves that every stage Tau preserves its handle count and actual source frame,
including acceptance/rejection and both trustee handshakes. Heterogeneous
equality records the dependent frame index without erasing it. The old-frame/
next-residual state is exactly the next canonical state under that index equality.

[SourceElectionOpeningInvariant](../../ExplainableCrypto/Helios/Symbolic/SourceElectionOpeningInvariant.lean)
transports the invariant and actual reductions across equal handle domains.
`source_opening_internal_next` consumes an arbitrary actual Named reduction and
the invariant, derives the next stage step, discharges determinism with the
existing full residual theorem, and returns the invariant for the actual next
source frame and body. The raw target is renamed by the explicit `Fin.cast`
induced by the proved equality of handle counts.

[SourceOpeningInternalTraces](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningInternalTraces.lean)
defines `PhaseOpening` to record this domain equality alongside the full opening
invariant. It holds at canonical phases, is stable under Structural, and is
preserved by actual Named internal reductions for fresh channels and in-range
phases. `PhaseOpening.internal_trace` handles any finite reflexive/transitive
sequence of actual Named reductions from a reached phase. It returns a reached
next phase, a corresponding sequence of stage Tau steps and the full invariant
on the final raw source target. Intermediate raw targets need no canonical
Structural presentation. The theorem concerns internal sequences; public inputs
and output captures are not included in this closure result.

## Controls, evidence and remaining obligations

[SourceTargetInvariantSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceTargetInvariantSPOT.lean)
contains 27 public kernel controls. Both conditional outcomes retain the full
invariant; active environments are preserved and wrong handle values are excluded.
Full SPK payloads and waiting inputs survive. A wrong branch is not a target
realization. The target can be refreshed again and its interpretation is
nonvacuous. A captured allocation fails external freshness. A parallel branch
and communication have two actual inequivalent outcomes, so dropping the
determinism premise is invalid. An actual two-step trustee sequence exercises
phase reachability, source actions and final invariant preservation. A public
publication changes handle count, excluding extension of the internal identity
lemma to outputs.

The gate uses general induction plus independently specified positive/negative
kernel controls. No new randomized cryptographic campaign or security evidence
from search failure is claimed. Figures 2–3 provide the source-action and scope
reference. Full E/E0, all cryptographic fields and explicit observations remain
unchanged; no custom axiom or source-action constructor was added.

Integrated verification: `lake build` passes **4030 jobs**. The log reports
**4247** nonempty standard-only and **86** axiom-free results. The claim audit
covers **3347** public theorem entries and **118** current-status documents.
All twelve changed Lean sources have current oleans; **1517** local links
resolve. No proof holes, custom axioms, warnings or errors were found in the
checked scope; `git diff --check` passes. This increment adds **59** theorem
audits, including **27** public kernel controls, and checks three new definitions.
The targeted control build passes **1402 jobs**.
Build log: `tmp/variable-overlap/source-target-invariant-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-target-invariant-verification.txt`.

Remaining: construct actions from arbitrary invariant representatives or prove
an adequate stronger reachable relation; close visible input/output invariants,
new output-frame presentation and coherent public-policy/coordinate matching;
then prove the full weak labelled bisimulation and symbolic secrecy theorem.
The existing both-world one-step matching and frame StaticEq theorems remain
proved, but internal invariant preservation alone is not a full bisimulation.
See the [blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and [task list.md](../../task%20list.md).
