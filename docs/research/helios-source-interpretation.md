# Equational process behavior and active-variable interpretation

B9 now has an interpretation of the current active-substitution/variable
fragment that survives every existing structural rule and recovers an actual
internal process step from every extended internal reduction. Canonical frame
endpoints preserve every complete handle value modulo full E. This is a
supporting converse for Extended, not the remaining Named correspondence or
full symbolic secrecy theorem. B9/B10 remain open at 8/10 milestones (80%, an
unweighted count, not an effort estimate).

## Equational behavior

[SourceEquationalFormula](../../ExplainableCrypto/Helios/Symbolic/SourceEquationalFormula.lean)
defines componentwise full-E congruence for guards, retaining equality versus
disequality and conjunction. It proves equivalence, substitution congruence and
truth preservation for both related guards and pointwise E-related environments.
[SourceEquationalProcesses](../../ExplainableCrypto/Helios/Symbolic/SourceEquationalProcesses.lean)
extends this to complete finite Agent syntax. Channels, constructors and both
continuations stay aligned. Input substitution respects the next binder and
E-equivalent messages throughout every nested continuation.

[SourceEquationalParallel](../../ExplainableCrypto/Helios/Symbolic/SourceEquationalParallel.lean)
proves that this congruence commutes in both directions with parallel structural
laws. Symmetric and transitive structural paths are included. Every CoreStep
and Tau has a matching actual step with an E-congruent target. Ground guards
use full EqE, including negative decisions; no normalization comparator is used.
[SourceEquationalVisible](../../ExplainableCrypto/Helios/Symbolic/SourceEquationalVisible.lean)
proves matching visible steps whose full payload events retain direction and
channel and have E-equivalent messages. Input can match a prescribed
E-equivalent message, including exactly the original term. Output does not
promise identical literal payload syntax: the retained output-label control
refutes that stronger assertion. These payload events are distinct from public
bound-handle output labels.

[SourceEvaluatedEquivalence](../../ExplainableCrypto/Helios/Symbolic/SourceEvaluatedEquivalence.lean)
defines EvalEq as parallel equivalence followed by process E-congruence. The
commuting squares prove symmetry and transitivity of this composite. It respects
parallel context and substitution and transports actual Tau/visible/input steps.
These relations are proof tools; no source operational rule or E equation changed.

## Interpreting active constraints

[SourceActiveInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceActiveInterpretation.lean)
defines `a.Realizes env p` recursively:

- A plain body realizes its environment substitution, modulo EvalEq.
- Active `x=M` requires `EqE (env x) (M.subst env)` and realizes Nil modulo EvalEq.
- Parallel components realize parallel bodies, modulo EvalEq.
- A restricted variable existentially chooses a ground value and extends env.

Output congruence and variable renaming are checked. The definition does not
assert that arbitrary cyclic or inconsistent constraints have a realization.
Actual complete frames do have one, as proved below.

[SourceInterpretationStructure](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationStructure.lean)
proves `Extended.Structural.realizes` for every existing constructor, including
Alias, SubstPlain, SubstActive, full-E Rewrite, New-Par, symmetry/transitivity and nested
contexts. Alias chooses the evaluated message; New-Par uses typed renaming to
avoid capture. SubstPlain is justified by its retained active equation and
complete process substitution congruence. The [general substitution increment](helios-source-general-substitution.md)
adds the active-active case: its retained provider equation gives full term
substitution congruence and preserves both active constraints. No syntactic closedness premise is
needed: discarded undefined variables introduced by legal Rewrite are handled
by the full-E constraint, without claiming their syntax becomes closed.

[SourceInterpretationReduction](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationReduction.lean)
proves `Extended.Reduction.realizes`: if a realizes p under env and a reduces
to b, there is q with `Agent.Tau p q` and b realizes q under the same env.
It covers atomic communication, ground Then/Else, contexts, existential locals
and arbitrary structural paths. The conclusion requires one real Tau, not an
empty sequence that could erase an enabled action.

[SourceInterpretationFrames](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationFrames.lean)
characterizes realization of actual finite frames exactly. Every handle value
must equal its environment value modulo E, and the frame contributes no active
process. For frameProcess φ a, realization is precisely those full handle
equations together with EvalEq a p. Consequently:

- Every actual frameProcess φ p realizes p under φ.value.
- An arbitrary extended reduction target has an interpreted actual Tau result.
- Canonical endpoints of arbitrary structural paths retain full handle E-values
  and related bodies. Canonical reduction endpoints retain those values and
  relate the target body to an actual Tau result.
- For a common restriction policy, these canonical frame endpoints have full
  Frame.StaticEq, using the existing pointwise-frame theorem.

This last observation concerns structural/internal preservation of a frame;
it does not replace the completed B7/B8 two-world ciphertext observation proofs.

## Controls, scope and next obligation

[SourceInterpretationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationSPOT.lean)
contains fifteen kernel controls: projection-equivalent but syntactically
distinct payloads, separate bits/channels/guard polarity, false negative
conjunctions, nested input binders, full receiver communication, combined
parallel/E laws, the literal output-label boundary, exact input matching,
outer-variable let evaluation, unsatisfied active constraints, the retained
nonclosed Rewrite example, a derived private communication beside the actual
old frame, and rejection of an altered full canonical frame value.

These are structural kernel proofs with independently specified positive and
negative controls. No new randomized cryptographic campaign or security
inference from failed attack search is claimed.

The subsequent [visible interpretation](helios-source-visible-interpretation.md)
now covers every current Extended free/bound action, with exact evaluated input
and the actual emitted message in the captured environment. Supplied canonical
targets retain all complete handle E-values. Next extend the interpretation and
canonical-target correspondence through Named name restrictions/alpha, using
[coherent fresh representatives](helios-source-fresh-names.md). Connect general
named-frame observations/admissibility and the outer voter nonce/let syntax,
then assemble source weak labelled bisimilarity and symbolic secrecy. General
replication, mobile channels and name creation under arbitrary plain prefixes
remain outside the current finite historical syntax.

See the [blueprint](helios-proof-blueprint.md),
[active source rules](helios-source-active.md),
[actual-frame input/internal derivations](helios-source-frame-input.md),
[well-formedness boundary](helios-source-wellformed.md) and
[task list](../../task%20list.md).

Integrated verification for the internal-interpretation checkpoint: `lake build` passes **3869 jobs**, with
**3118** nonempty standard-only and **48** axiom-free reports. The claim audit
covers **2180** public theorem entries and **93** current-status documents.
All twelve changed Lean sources have current oleans; **1162** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-interpretation-full-build.log`.
This increment adds 82 theorem audits, including fifteen kernel controls, and
five definition checks. Targeted controls pass 1219 jobs. Freshness/hole/link
evidence: `tmp/variable-overlap/source-interpretation-verification.txt`.

[Exact extended instantiation](helios-source-local-normalization.md) now
transports the entire realizing environment and specified body in both
directions. Local elimination evaluates the provider in the old environment
and extends it by that value. This does not yet establish canonical
environment/body correspondence across arbitrary Named structural paths.
