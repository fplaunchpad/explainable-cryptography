# Structural opening comparison and fresh internal matching

Current follow-up: [structural action openings](helios-source-structural-openings.md)
retain actual binder-structural endpoint paths and characterize Named structure
by jointly fresh structural openings. General reachable reconstruction and
final secrecy remain open.

Current update: [binder rigidity](helios-source-binder-rigidity.md) now proves
full Named.Structural separation of the cyclic joint pair and excludes all its
ground frame presentations/StaticEq partners. Structural opening comparison is
stronger, and Extended bound-output rigidity is checked. Earlier statements
leaving these facts open below are historical; reconstruction sufficiency remains open.

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

Status: **machine-checked** B9 increment. Every original Named Structural rule
preserves chosen fresh openings up to equality of full realizations. Every
actual internal reduction from a canonical structural representative yields a
canonical Tau and a full interpretation of the raw target in coherent fresh
coordinates. Reached election states have actual one-step matching in either
vote world, including check branches, and statically equivalent targets.
B9/B10 remain incomplete: 8/10 unweighted milestones (80%). The relation needed
to repeat this matching and the final symbolic secrecy theorem remain open.

## The comparison property

[SourceSameRealizations](../../ExplainableCrypto/Helios/Symbolic/SourceSameRealizations.lean)
defines `Extended.SameRealizations a b` by quantifying all ground environments
and complete process bodies: `a.Realizes env p ↔ b.Realizes env p`. Active
substitution equations, variable binders, full guards, payloads and continuations
all remain in this predicate. Its context lemmas include variable-binder exchange.
It is proof instrumentation and adds no source structural or reduction rule.

[SourceOpeningTransport](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningTransport.lean)
defines `Named.OpeningTransport a b`: any opening of `a` whose allocations avoid
a supplied finite set has an opening of `b`, under the same outer assignment,
avoiding that set and with exactly the same full realizations. The allocation
lists need not be identical: an unused restriction can add or remove a name.
`OpeningEquivalent` requires transport in both directions. Distinctness is
retained by the existing `Opens` constructors. Parallel contexts enlarge the
avoidance set by their other allocation list; name contexts add the current
allocation. No global injectivity premise is needed for structural comparison.

[SourceOpeningInversion](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningInversion.lean)
proves inversion under variable renaming and source-name permutations.
[SourceOpeningParallelComparison](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningParallelComparison.lean)
covers embedded Extended structural derivations, zero, commutativity,
associativity and embedding contexts.
[SourceOpeningAlphaComparison](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningAlphaComparison.lean)
proves that actual alpha rules preserve the same allocation and complete body,
using the original allNames freshness side condition.
[SourceOpeningNameComparison](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningNameComparison.lean)
covers unused restrictions, name exchange, name/variable exchange and extrusion;
[SourceOpeningVariableComparison](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningVariableComparison.lean)
covers variable extrusion and exchange, retaining all active constraints.

[SourceStructuralOpeningComparison](../../ExplainableCrypto/Helios/Symbolic/SourceStructuralOpeningComparison.lean)
proves `Named.Structural.openingEquivalent` by induction over every original
constructor. `transport_opening` exposes its one-direction application. This
closes the structural-comparison obligation left by the
[fresh opening construction](helios-source-openings.md).

## From an actual source action to canonical Tau

[SourceOpeningInternalInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningInternalInterpretation.lean)
first proves `Opens.prefix_reduction_realizes`. Given an actual Extended reduction
under a pure name prefix, an outer assignment faithful on both endpoint supports,
and allocations avoiding their assigned support image, every full realization
of the chosen source opening yields an actual Tau and a full interpretation of
the restricted target. Fresh assignment updates maintain finite faithfulness
down the prefix. Both conditional polarities use the unchanged original action
rules and full E. There is no assumption about intermediate derivation support.

`Reduction.opening_interpretation` starts with an arbitrary original Named
reduction. Its existing prenex factorization supplies an actual Extended action;
the union of the two endpoint supports supplies sufficient finite avoidance.
Structural opening comparison transports the chosen source opening to that
factored source. The prefix theorem acts on its full realization, and the actual
target structural path reconstructs the full interpretation of the raw target.
The finite avoidance set is constructed from the action, not supplied as a
missing operational-correspondence witness.

[SourceFreshCanonicalInternal](../../ExplainableCrypto/Helios/Symbolic/SourceFreshCanonicalInternal.lean)
combines that result with `exists_fresh_canonical_opening`.
`Reduction.fresh_canonical_interpretation` starts with an arbitrary actual
reduction `a → b` and an actual Structural path from a canonical state to `a`.
It constructs a distinct fresh allocation, an actual canonical source opening,
permutations `e,k`, an exact full mapped frame process and an actual Tau of the
mapped canonical body. The unchanged raw target `b` interprets the complete
resulting body in the mapped frame environment. Any additional finite set can
be avoided. Neither an injective witness nor a guard-recovery witness is assumed.

`Reduction.canonical_tau` applies the inverse permutations to the actual Tau,
yielding a Tau of the original canonical body. Its raw target interpretation
continues to use the coherently mapped environment and mapped target body.
This does not assert that the raw target interprets that body in the old fixed
environment. The retained dead-field/fixed-environment counterexample still
applies. Public-policy fixation or coordinated witnesses across repeated actions
are not conclusions of these theorems.

## Election matching and its remaining boundary

[SourceFreshElectionInternal](../../ExplainableCrypto/Helios/Symbolic/SourceFreshElectionInternal.lean)
proves `source_fresh_internal_interpreted`: for fresh channels and an in-range
phase, every actual Named internal action from a canonical structural
representative yields a stage Tau and a full interpretation of the raw target's
next residual in one coherently permuted old frame environment. This includes
the check phase and both branches; it has no communication-only or non-check
premise.

`reachable_source_fresh_internal_matching` also assumes fresh election names
and a reached phase. Both world inputs may be arbitrary structural
representatives of their respective canonical states. It constructs a reached
next phase, an actual Named reduction in the other vote world, the full target
residual, the raw target's coherent interpretation, and Named.StaticEq between
the two targets. Static equivalence uses the existing full source frame
presentations and internal frame preservation, with all public tests quantified.
The swap booleans are arbitrary, so either direction is covered.

This proves a one-step matching statement. Its raw target is not proved
structurally equivalent to the next canonical state or a member of an invariant
relation that would support the next invocation. The other target is indexed
by the original phase's handle domain and old frame, with the next residual.
The required domain/frame identification, target/relation closure, coherent
policy/coordinate invariants and bound output's new-frame structural presentation
remain open. No weak labelled bisimulation or final symbolic secrecy claim is
made from this one-step result.

## Controls and evidence

[SourceOpeningComparisonSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningComparisonSPOT.lean)
contains 23 public kernel controls. Positive fixtures cover unused-binder
transport with arbitrary avoidance, actual extrusion, base/channel alpha,
variable exchange, same-spelling shadowing, distinct sorts, an E projection
rewrite retaining active constraints, both actual conditional outcomes and a
nonvacuous canonical conditional with constructed raw-target witnesses.
Negative fixtures exclude identical allocation lists after removing a binder,
capturing extrusion/alpha, equating different active values, captured endpoint
allocation and spurious internal reduction of a quiet canonical process through
arbitrary structural representatives. Full SPK fourth fields remain observable
in support and are excluded as alpha targets where appropriate.

The gate is general structural/prefix induction plus independently specified
positive/negative kernel controls. No new randomized cryptographic campaign,
exhaustive search or security inference from search failure is claimed. Figures
2–3 alpha, New, extrusion, structural congruence and communication/conditionals
provide the reality reference; source actions and full E/E0 are unchanged.
The formal oracle is the public theorem statement and its checked axioms.

Integrated verification: `lake build` passes **4020 jobs**. The log reports
**4189** nonempty standard-only and **85** axiom-free results. The claim audit
covers **3288** public theorem entries and **117** current-status documents.
All fourteen changed Lean sources have current oleans; **1498** local links
resolve. No proof holes, custom axioms, warnings or errors were found in the
checked scope; `git diff --check` passes. This increment adds **70** theorem
audits, including **23** public kernel controls, and checks three comparison
definitions. The targeted control build passes **1392 jobs**.
Build log: `tmp/variable-overlap/source-opening-comparison-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-opening-comparison-verification.txt`.

See the [blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and [task list.md](../../task%20list.md).
