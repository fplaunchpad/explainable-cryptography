# Visible actions and captured environments

B9 now interprets every current Extended free and bound visible action,
including arbitrary active/variable structural paths. Inputs use exactly the
evaluated recipe. Bound outputs extend the target environment with the actual
complete emitted message while retaining all previous values. This completes
the visible interpretation obligation for the current Extended fragment;
Named restrictions/alpha, canonical-target existence and the full source
secrecy correspondence remain open. B9/B10 remain at 8/10 completed milestones
(80%, unweighted, not an effort estimate).

## Ground environments and labels

[SourceInterpretationEnvironment](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationEnvironment.lean)
proves that Realizes is invariant under pointwise full-E changes to its ground
environment. This preserves complete active equations, interpreted continuations
and existential locals. `extend_congr` changes only the fresh value modulo E;
`shiftTerm_eval` evaluates a shifted recipe independently of the new local.
`extendEnv_swapBinders` exchanges the fresh exported value with an enclosing
restricted local, retaining every older variable.

[SourceInterpretedLabels](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretedLabels.lean)
defines `FreeLabel.RealizedStep`. An input label carries exactly its evaluated
recipe. An atomic output carries an actual emitted message E-equivalent to the
label variable's environment value. Parallel context and EvalEq transport
preserve this distinction; there is no accidental weakening of exact input
matching to an arbitrary E-equivalent input.

## Every current visible rule

[SourceInterpretationFree](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationFree.lean)
proves `FreeStep.realizes` and explicit input/output corollaries. Given a source
realization, In and Out-Atom produce actual visible actions and a realized raw
target. Variable Scope, both parallel contexts and arbitrary Structural closure
are included. The source and target use the same environment. Input evaluates
the entire term, with typed nested binding and the original recipe preserved
in the source label.

[SourceInterpretationBound](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationBound.lean)
proves `BoundOutput.realizes`: from a realization under env there exist an
actual emitted message m and actual visible continuation q, and the raw target
realizes q under `extendEnv env m`. Open-Atom may start with an E-equivalent
local representative; environment congruence changes it to the actual emitted
message. Variable Scope performs the checked binder exchange. Parallel
contexts are shifted with Some and retain their previous values; Struct uses
the existing interpretation-preservation theorem. All constructors are covered.

No source rule, equation or public observation was removed or weakened.
These are interpretation results for the current finite static-channel syntax,
not new primitive operational rules.

## Actual frames and complete capture

[SourceInterpretationVisibleFrames](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationVisibleFrames.lean)
applies the general results to actual finite frames. Inputs to arbitrary raw
targets have actual visible behavior at exactly `φ.eval recipe`. If the target
is canonical, every handle retains its complete E-value and the target body
is EvalEq-related to the actual visible continuation. A common-policy canonical
input target has full Frame.StaticEq with the original frame.

A bound-output raw target realizes the actual continuation under the original
frame extended with the emitted message. After explicit `outputHandle` renaming,
it realizes that same continuation under `(φ.extend m).value`. If a structural
path to a canonical target is supplied, every old and new handle in that target
matches the extended frame modulo E. At a common restriction policy, this
implies full Frame.StaticEq. These conditional canonical-target results do not
assert that an arbitrary target already has the required canonical structural
representative; that existence/correspondence work remains open.

[SourceInterpretationCapture](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationCapture.lean)
characterizes a capture exactly: the fresh environment value equals the entire
evaluated message modulo E, and the old continuation is evaluated under the
unchanged old environment, modulo EvalEq. Ground capture retains precisely its
full ground term. No tally summary or redaction substitutes for that value.

## Controls and remaining work

[SourceVisibleInterpretationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleInterpretationSPOT.lean)
has fourteen kernel controls. They include E-equivalent capture environments,
rejection of an incorrect new value, a concrete binder exchange and rejection
of omitting it, output through a restricted local with distinct values, an
independently realized scoped target, unchanged old handles and rejection of
changing one through any post-output structural path. An actual handle recipe
input preserves its evaluated key and frame observations. A projection-wrapper
output realizes its E-equivalent bit capture. A deliberately mismatched proof
fixture retains all four proof fields in its full frame value; derived output
preserves its complete frame observations. The actual first election publication
has an interpreted captured target under the actual emitted ballot environment.
The proof fixture tests output semantics, not proof acceptance or security.

The evidence is general structural kernel proofs with independent positive and
negative controls. There is no new randomized cryptographic campaign and no
security inference from failed attack search. The earlier literal-output-label
and nonclosed-Rewrite boundaries remain intact.

The subsequent [name-interpretation/prenex construction](helios-source-name-interpretation.md)
now gives consistent environment transport/reflection and a fresh distinct
outer name prefix for every finite Named process. Next interpret whole Named
base/channel restriction and alpha derivations using those representatives and
[coherent fresh policies](helios-source-fresh-names.md).
Recover appropriate target representatives and connect general named-frame
observations/admissibility and outer voter nonce/let syntax. Then assemble source
weak labelled bisimilarity and symbolic secrecy. Fresh source existence alone
does not normalize a whole Named derivation. General replication, mobile
channels and name creation under arbitrary plain prefixes remain outside the
current finite historical syntax.

See the [blueprint](helios-proof-blueprint.md),
[internal/structural interpretation](helios-source-interpretation.md),
[atomic output and active frames](helios-source-atomic-output.md),
[name restrictions](helios-source-name-restrictions.md) and
[task list](../../task%20list.md).

Integrated verification for the visible-interpretation checkpoint: `lake build` passes **3876 jobs**, with
**3156** nonempty standard-only and **48** axiom-free reports. The claim audit
covers **2218** public theorem entries and **94** current-status documents.
All nine changed Lean sources have current oleans; **1178** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-visible-interpretation-full-build.log`.
This increment adds 38 theorem audits, including fourteen kernel controls, and
one definition check. Targeted controls pass 1226 jobs. Freshness/hole/link
evidence: `tmp/variable-overlap/source-visible-interpretation-verification.txt`.
