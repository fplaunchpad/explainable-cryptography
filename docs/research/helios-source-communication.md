# Named internal communication and election matching

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

Current guard frontier: [equational recovery](helios-source-guard-retractions.md)
now supplies a sufficient truth-preservation condition that handles unused-field
collisions. Coherent Named witnesses and final secrecy remain open. Earlier
guard-boundary statements below describe their checkpoint.

Current internal frontier: [exact conditional location and arbitrary non-check
matching](helios-source-conditional-location.md) are now proved. Check-phase
truth correspondence, required target invariants and final secrecy remain open.
Earlier internal-boundary statements below describe their checkpoint.

Status: **machine-checked** B9 increment. General forward communication
interpretation and communication matching from reached source representatives
are proved. B9/B10 remain incomplete at 8/10 unweighted milestones (80%).
The final symbolic secrecy theorem remains unproved.

## Exact classification of the existing rules

[SourceClassifiedInternal](../../ExplainableCrypto/Helios/Symbolic/SourceClassifiedInternal.lean)
defines `InternalKind` and classified `Extended.InternalStep` and
`Named.InternalStep` derivations. A tag records the primitive communication,
successful conditional or failed conditional beneath the existing contexts.
Both `Reduction.classify` theorems cover every constructor of the original
internal relation; `InternalStep.reduction` erases a tag back to that relation.
The resulting equivalences are exact. They do not assert that two derivations
between the same endpoints have a unique tag. No protocol action is added.

## General forward interpretation

[SourceCommunicationInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceCommunicationInterpretation.lean)
proves that Extended communication maps forward under arbitrary base-name and
channel assignments. A communication uses equal channels before mapping, so
their images remain equal. It does not test a ground guard. The theorem covers
all structural pre/post paths and active substitutions, not just literal
output/input pairs.

`Named.InternalStep.communication_interprets` transports any full
`Named.Interprets` witness through every Named context. It gives an actual
`Agent.Tau` and the full raw target interpretation under the same outer
assignment/environment. Name and variable binders retain their chosen witnesses;
parallel contexts retain waiting threads. No global or finite injectivity
premise remains in this communication theorem.

`Named.Reduction.interprets_or_conditional` is exhaustive: an arbitrary original
reduction either has such an interpreted Tau and full target, or has a
classified conditional derivation. The conditional alternative is explicit;
this is not an unconditional interpretation theorem for all internal steps.
`communication_canonical` also retains the old frame and the actual raw
target's `RepresentsFrame` witness for a canonical source representative.

## Actual election matching

[SourceElectionCommunicationMatching](../../ExplainableCrypto/Helios/Symbolic/SourceElectionCommunicationMatching.lean)
connects a communication from an interpreted, in-range election to an actual
internal stage transition. The target interprets the complete next residual
under the original frame environment.

`reachable_source_communication_matching` takes fresh names/channels, a reached
phase, arbitrary structural representatives in two voting worlds, and an actual
classified communication in the first world. It constructs an actual
`Named.Reduction` from the other representative, a reachable next phase, and
`Named.StaticEq` between the original raw target and the matching target.
It retains the original raw target's full next-body interpretation. The
matching state has the other world's old frame and the complete next residual,
indexed by the old phase's handles. No internal-correspondence callback is
assumed. The proof uses the checked stage swap invariant and frame equivalence.

This result does not claim that every target is structurally canonical or that
the final bisimulation relation is closed under subsequent actions. Required
target presentations and relation invariants remain separate obligations.

[SourceClassifiedCommunication](../../ExplainableCrypto/Helios/Symbolic/SourceClassifiedCommunication.lean)
derives full-message communication using the actual variable-alias, active
Subst and restriction rules; it also handles ground and guarded-program
communication. [SourceClassifiedElection](../../ExplainableCrypto/Helios/Symbolic/SourceClassifiedElection.lean)
classifies actual first-voter delivery and trustee tally delivery with the
complete continuation and reply thread.

## Controls, assumptions and evidence

[SourceCommunicationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceCommunicationSPOT.lean)
has twenty-one public kernel controls. Positive controls retain all four SPK
fields through a private communication, interpret a communication even when
channels collide, classify actual voter/trustee actions, and instantiate the
either-world matching result with an actual source action. Successful and
failed guards have distinct tags and erase to the existing reduction rules.
Negative controls exclude communication between distinct channels, any
classified step from the empty process, and communication from a rejected
election. A channel collapse can create a new communication, so forward
transport does not imply reflection. The existing ground-name collision
control changes guard truth and retains the remaining conditional obstruction.

Communication interpretation assumes a full source interpretation. Election
matching additionally assumes the stated freshness, reachability and structural
representatives. Its actual source communication premise is independently
inhabited by the voter controls; it is not an assumed matching conclusion.
General inductions and directed positive/negative controls form this gate.
No new randomized cryptographic campaign or inference from search failure is
claimed. Cortier–Smyth Figure 3 and the existing source action rules supply the
reality reference. Full E/E0, structured-key E5, full-ciphertext E6 and explicit
public observations remain unchanged. No custom axiom is added.

Integrated verification: `lake build` passes **3990 jobs**. The log reports
**3989** nonempty standard-only and **75** axiom-free results. The claim audit
covers **3078** public theorem entries and **113** current-status documents.
All eight changed Lean sources have current oleans; **1458** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **48** theorem audits,
including **21** public kernel controls, and checks the three classified-derivation types. The targeted control build passes **1362 jobs**.
Build log: `tmp/variable-overlap/source-communication-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-communication-verification.txt`.

Remaining: arbitrary Named conditional correspondence; required target
presentation and relation invariants; final source weak labelled bisimilarity
and symbolic secrecy. The earlier finite-injectivity lemma remains a sufficient
internal transport result, but its fixed-environment witness cannot always
exist after alpha-renaming and dead-field rewriting. That false strengthening
must not be introduced as an undischarged premise of the secrecy theorem.
Maintain the [blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md), and existing B9/B10 item in
[task list.md](../../task%20list.md).
