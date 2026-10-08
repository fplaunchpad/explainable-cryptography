# Equational name recovery for source guards

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

Status: **machine-checked** B9 increment. Recovery of complete guard operands
modulo E suffices for truth preservation and full mapped internal targets.
This sufficient condition is not yet discharged for arbitrary Named check paths.
B9/B10 remain incomplete at 8/10 unweighted milestones (80%); final symbolic
secrecy remains unproved.

## Semantic recovery instead of literal recovery

[SourceGuardRetractions](../../ExplainableCrypto/Helios/Symbolic/SourceGuardRetractions.lean)
defines `Term.NameRetracts t f g` as full `EqE` between `t` and the result of
mapping its names by `f` and then `g`. The original complete term is retained.
This condition does not require literal recovery of every syntactic name.
It is invariant under full E and closed under every term constructor, with
all four SPK fields required by the constructor lemma.

`EqE.mapNames_iff_of_retractions` reflects equality between two recovered
terms by applying the inverse map to the equality proof. Forward equality uses
ordinary full-E name-map stability. `Formula.NameRetracts` requires componentwise
full-E recovery of every operand, preserving equality/disequality polarity and
conjunction. `holds_mapNames` proves equivalence of guard truth in both
directions, so both Then and Else are supported. A genuine name permutation
always supplies such a recovery map.

[SourceRetractionSubstitution](../../ExplainableCrypto/Helios/Symbolic/SourceRetractionSubstitution.lean)
derives recovery from a left inverse on literal support, and proves it survives
substitution when both the formula/term and substituted values recover.
`holds_mapped_environment` moves the entire ground environment consistently.
It does not assume an unchanged environment when its names have moved.

## Actual internal steps and election guards

[SourceReadyGuardRetractions](../../ExplainableCrypto/Helios/Symbolic/SourceReadyGuardRetractions.lean)
checks only currently ready guards. Input/output prefixes and branch
continuations are not recovery premises for this single step. Parallel structure,
full process E-congruence and `EvalEq` preserve this condition.
`CoreStep.mapNames_of_guard_retractions` and
`Tau.mapNames_of_guard_retractions` transport an actual step to its complete
mapped target, selecting the same branch. Channel maps may be arbitrary: this
is forward transport, not reflection of newly created communications.

[SourceRetractedInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceRetractedInterpretation.lean)
first interprets an actual Extended reduction, then transports its evaluated
Tau and complete target interpretation using the ready-guard condition.
The environment moves with the base-name map. This theorem does not construct
an original Extended realization from an arbitrary Named representative.

[SourceElectionGuardRetractions](../../ExplainableCrypto/Helios/Symbolic/SourceElectionGuardRetractions.lean)
proves recovery through tuple projection/drop and the nonempty homomorphic
aggregate, then through the complete literal finite election guard. Its premises
recover the key, each full board ballot and the incoming ballot. The conclusion
includes aggregate and component proof checks, the corrected tail test and every
cross-candidate replay comparison. There is no ballot-validity assumption:
malformed terms and both outcomes remain covered. The check-state Tau corollary
retains the complete mapped residual target under these explicit premises.

## Decisive controls and limits

[SourceGuardRetractionSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceGuardRetractionSPOT.lean)
has twenty-one public kernel controls. Map 50 to 40 while leaving 40 fixed;
map 40 back to 50 for recovery. The term `fst(pair(50,40))` recovers modulo E,
although its syntax does not recover and the original finite injectivity
condition remains false. Equality to 50 and disequality from 41 both retain
their truth. Actual true/false conditionals preserve their chosen complete
continuations. A literal replay-check reduction also instantiates the election
transport theorem with actual permutations.

Colliding essential names 50 and 40 cannot both recover under any inverse map.
A proof with an unrecovered fourth field and a ciphertext with an unrecovered
plaintext field fail the same test, using full-E constructor injectivity.
The full output payload is still transported when its own recovery is not a
premise: no field is dropped. An unrecovered future guard can remain below an
output prefix during the current step. This is an explicit one-step boundary;
recovery is not asserted to persist through every later action.

The gate combines general algebra/structural induction with independently
specified positive/negative kernel controls. No new randomized cryptographic
campaign or search-failure evidence is claimed. Figure 3 full-E conditionals
and the earlier legal active-substitution unused-field rewrite supply the
reality reference. E/E0, structured-key E5, full-ciphertext E6, SPK fields,
source action rules and public observations remain unchanged. No custom axiom
or replacement action semantics is added.

Integrated verification: `lake build` passes **4001 jobs**. The log reports
**4079** nonempty standard-only and **79** axiom-free results. The claim audit
covers **3172** public theorem entries and **115** current-status documents.
All eight changed Lean sources have current oleans; **1473** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **50** theorem audits,
including **21** public kernel controls, and checks the three recovery definitions. The targeted control build passes **1373 jobs**.
Build log: `tmp/variable-overlap/source-guard-retraction-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-guard-retraction-verification.txt`.

Remaining: choose coherent recovery witnesses or another sufficient argument
through arbitrary Named check paths; establish required target presentations
and relation invariants; prove final source weak labelled bisimilarity and
symbolic secrecy. The fixed-old-environment syntactic-injectivity conjecture
remains refuted. The new sufficient condition is not a completed Named witness
construction. See the [blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and [task list.md](../../task%20list.md).
