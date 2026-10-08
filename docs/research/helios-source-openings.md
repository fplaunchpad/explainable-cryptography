# Fresh name openings and canonical witnesses

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

Status: **machine-checked** B9 increment. Chosen sufficiently fresh openings
are actual source representatives; fresh canonical openings construct full
frame/body permutation witnesses. Comparison through arbitrary structural/action
paths is still open. B9/B10 remain incomplete at 8/10 unweighted milestones (80%).
Final symbolic secrecy remains unproved.

## The opening witness

[SourceNameOpening](../../ExplainableCrypto/Helios/Symbolic/SourceNameOpening.lean)
defines `Named.Opens a ρ ns b`. It recursively assigns a numeric value to each
removed name binder while retaining its base/channel sort, records allocations
in `ns`, and produces one complete Extended body `b`. Parallel allocations are
disjoint and a binder's allocation differs from every nested allocation.
Therefore `ns` is globally duplicate-free, even with shadowed source spellings.
Variable binders and active definitions remain in the Extended body. Full code,
guard operands and input/output continuations are retained.

`exists_fresh_opening` avoids any finite external set. `names_congr` depends
only on agreement at free names; variable renaming is compatible with opening.
`Opens.interprets` reconstructs the original full Named interpretation from any
realization of the opened body, in the same environment and with the complete
continuation. This is not an interpretation-to-opening converse.

[SourceOpeningSupport](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningSupport.lean)
proves that every output name is an assigned free source name or an explicit
allocation. All fields count. The opening relation itself records distinct
allocations but does not require external freshness: a fresh-allocation theorem
or an explicit freshness premise must exclude capture of a free name.

## Actual source derivation

[SourceOpeningAlpha](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningAlpha.lean)
handles assignment agreement and freshness through actual same-sort alpha swaps.
[SourceOpeningDerivation](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningDerivation.lean)
proves `Opens.structural`: when the outer assignment agrees with base/channel
permutations on free source names and all chosen allocations avoid the complete
mapped source support (including binders), the opening is an actual Structural
prenex representative of that mapped source.

The proof uses the existing alpha, name/variable extrusion, embedding and
parallel rules. It does not add a source equation or action. Literal assignment
gives `structural_literal`, and `exists_fresh_opening_structural` constructs a
fresh, duplicate-free opening and its actual Structural path together.
Unlike the earlier existence-only prenex theorem, this result validates the
particular allocation and body carried by an `Opens` witness.

## Constructed canonical recovery

[SourceOpeningFaithfulness](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningFaithfulness.lean)
proves that assigning a name outside the current finite image preserves finite
faithfulness. Opening a restriction prefix yields one assignment for its entire
Extended body, fixed outside that prefix. Distinct allocations outside the
initial finite image construct a faithful final assignment. The proof tolerates
shadowed original binder spellings; allocations remain distinct.

For literal assignment and allocations fresh for the original Extended support,
`prefix_permutations` uses the checked Mathlib finite extension result to produce
actual base/channel permutations describing the opened body. It does not claim
those permutations fix every name outside that finite support.

[SourceCanonicalOpening](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalOpening.lean)
applies this to a canonical full state. Every appropriately fresh opening has
exactly the frame process of its original frame and body under two derived
permutations. It has a literal Extended realization in the permuted frame
environment, and the permutation inverse supplies ready-guard retractions.
`exists_fresh_canonical_opening` packages actual source derivability, arbitrary
finite avoidance, distinct allocation, exact frame/body equality, full realization
and guard recovery. No permutation or recovery witness is an input premise.

This permits a coherently renamed environment. It does not restore the refuted
requirement to keep an old exported value while fixing every newly introduced
free literal. The missing connection is comparison of openings across arbitrary
Structural/action derivations, so that the actual action's factored body can use
the coherent canonical realization. Constructing one canonical opening alone
does not prove that connection or check-phase correspondence.

## Controls and evidence

[SourceOpeningSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceOpeningSPOT.lean)
has eighteen public kernel controls. They cover full private SPK output with a
waiting input, actual alpha/extrusion, parallel binders with the same source
spelling and distinct values, nested shadowing, retained variable constraints,
interpretation reconstruction, arbitrary finite avoidance, and constructed
canonical/election-check witnesses. Two different sorts may use the same numeral;
two same-sort allocations cannot. An externally colliding opening can capture
a free literal and change guard truth. It fails the structural theorem's
freshness premise, making that boundary explicit.

The gate uses general constructor/structural proofs with independently specified
positive/negative kernel controls. No new randomized cryptographic campaign or
search-failure evidence is claimed. Figures 2–3 alpha, extrusion and New contexts
supply the reality reference. Full E/E0, cryptographic fields and observations
are unchanged. Opening is proof instrumentation, not a replacement protocol
semantics. No custom axiom is added.

Integrated verification: `lake build` passes **4008 jobs**. The log reports
**4121** nonempty standard-only and **83** axiom-free results. The claim audit
covers **3218** public theorem entries and **116** current-status documents.
All nine changed Lean sources have current oleans; **1487** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **46** theorem audits,
including **18** public kernel controls, and checks the three opening definitions. The targeted control build passes **1380 jobs**.
Build log: `tmp/variable-overlap/source-opening-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-opening-verification.txt`.

Remaining: opening comparison through arbitrary structural/action paths and
coherent check correspondence; required target presentations/relation invariants;
final weak labelled bisimilarity and symbolic secrecy. See the
[blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md) and
[task list.md](../../task%20list.md).
