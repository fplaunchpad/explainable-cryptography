# Conditional location and arbitrary non-check source matching

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

Status: **machine-checked** B9 increment. Every original Named internal reduction
outside the election check phase is classified as communication and has the
actual either-world matching result. Check-phase truth correspondence and the
final symbolic secrecy theorem remain unproved. B9/B10 remain incomplete at
8/10 unweighted milestones (80%).

## Readiness through every source context

[SourceConditionalReadiness](../../ExplainableCrypto/Helios/Symbolic/SourceConditionalReadiness.lean)
defines `Agent.HasConditional`, a syntax predicate: parallel composition joins
readiness, a branch is ready, and input/output prefixes block it. This predicate
is equivalent to an actual branch in the flattened active threads. It does not
authorize either branch or discard a guard's truth requirement. Substitution,
arbitrary name maps, parallel structure, full process E-congruence and their
`EvalEq` composite all preserve it.

[SourceConditionalLocation](../../ExplainableCrypto/Helios/Symbolic/SourceConditionalLocation.lean)
proves `Extended.InternalStep.conditional_realizes_ready` and
`Named.InternalStep.conditional_interprets_ready` for every classified
conditional derivation. The latter includes every structural pre/post path,
name binder, variable binder and parallel context. Both successful and failed
conditionals require readiness in every full interpreted body. No assignment
injectivity premise is used. Thus `Named.Reduction.communication_of_no_conditional`
extracts an actual communication derivation from an arbitrary original reduction
when the interpreted body has no ready conditional. Its interpreted Tau and
complete target follow from the checked communication theorem.

## Exact election location and matching

[SourceElectionConditionalLocation](../../ExplainableCrypto/Helios/Symbolic/SourceElectionConditionalLocation.lean)
proves `residual_hasConditional_iff`: readiness occurs exactly at `.check rs r`.
This syntax result needs neither reachability, range nor channel freshness.
Even an exhausted collection input phase has an output head, so no guard is
ready there. All original source reductions from an interpreted election are
therefore classified communications or originate at that exact check phase.

`reachable_source_noncheck_internal_matching` takes an arbitrary original
`Named.Reduction`, fresh names/channels, a reached non-check phase and arbitrary
structural representatives in the two voting worlds. It derives communication
internally, then constructs an actual matching Named reduction, a reachable
next phase, the full original raw target's interpretation, and `Named.StaticEq`
between actual targets. Its matching state contains the other world's old frame
and complete next residual, indexed by the old handles. There is no assumed
communication or internal matching callback.

The explicit non-check premise is essential to the present proof. An actual
check is ready and has an accepting or rejecting reduction. This increment
locates that obligation; it does not prove the chosen source guard's truth is
preserved under the interpretation. Nor does the matching theorem assert
structural canonicalization or closure of the final bisimulation relation.

## Source phases that cannot reduce internally

[SourceNamedQuietPhases](../../ExplainableCrypto/Helios/Symbolic/SourceNamedQuietPhases.lean)
lifts evaluated quietness and absence of ready conditionals to exclusion of
**every original Named internal reduction**, through arbitrary structural
representatives and with arbitrary raw targets. First/second public ballot
relays require fresh channels; pending voter input requires an unexhausted
history. Partial/result publications and completed elections need neither
extra premise. The rejected-state theorem in SourceElectionConditionalLocation
also needs neither range nor freshness. Rejection retains the waiting trustee;
the result does not replace it with an empty process.

## Controls and evidence

[SourceConditionalLocationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceConditionalLocationSPOT.lean)
has nineteen public kernel controls. Positive cases include a ready false guard,
a private successful conditional, an actual first-voter reduction instantiating
the stronger matching theorem, and actual accepting and rejecting source check
reductions. Negative cases retain input/output barriers, exclude internal steps
from pending input/publication and rejected/completed states, and show that a
check cannot satisfy the non-check premise. An exhausted input's lack of a ready
guard does not imply it is internally quiet: the range condition for quietness
is retained. Existing channel and guard collision counterexamples remain valid.

The gate uses general structural induction and independently specified literal
positive/negative kernel controls. No new randomized cryptographic campaign or
evidence from search failure is claimed. Figure 3 evaluation contexts and the
Figure 4 board guard placement supply the reality reference. Source rules,
full E/E0, complete cryptographic fields and explicit observations are unchanged.
No custom axiom or unguarded operational rule is added.

Integrated verification: `lake build` passes **3995 jobs**. The log reports
**4032** nonempty standard-only and **76** axiom-free results. The claim audit
covers **3122** public theorem entries and **114** current-status documents.
All seven changed Lean sources have current oleans; **1470** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **44** theorem audits,
including **19** public kernel controls, and checks the readiness definition. The targeted control build passes **1367 jobs**.
Build log: `tmp/variable-overlap/source-conditional-location-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-conditional-location-verification.txt`.

Remaining: check-phase truth correspondence through arbitrary source paths;
required target presentation and relation invariants; final weak labelled
bisimilarity and symbolic secrecy. Finite syntactic injectivity at a fixed
old environment remains refuted by the retained alpha/dead-field example.
Maintain the [blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and B9/B10 item in
[task list.md](../../task%20list.md).
