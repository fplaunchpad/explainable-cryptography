# Complete frames of general named source processes

B9 now has a frame projection for every current Extended and Named process.
It retains all active substitutions, complete payload terms, and name/variable
restrictions, replacing plain process leaves with Nil. Every structural rule
transports to these frames. Internal and free actions preserve them up to
Structural; restricting the freshly exported variable after bound output
recovers the source frame up to Named Structural. These are machine-checked
source-model results. Canonical interpretation across arbitrary Named
representatives and the final symbolic secrecy theorem remain open. B9/B10
remain incomplete at 8/10 milestones (80%, unweighted).

## Projection and structural transport

[SourceExtendedFrameProjection](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedFrameProjection.lean)
defines `Extended.frameOf` and proves idempotence, commutation with variable and
name maps, exact preservation of exported variables, and containment of name
support. Active payloads retain their complete original syntax, including all
four proof arguments.

[SourceNamedFrameProjection](../../ExplainableCrypto/Helios/Symbolic/SourceNamedFrameProjection.lean)
defines `Named.frameOf`, retains every name restriction, and proves idempotence,
commutation with variable/name maps and restriction prefixes, and containment
of free/all names. Containment applies to extraction of each representative;
it does not claim that raw Rewrite preserves all syntactic free base names.

[SourceFrameStructure](../../ExplainableCrypto/Helios/Symbolic/SourceFrameStructure.lean)
proves `Extended.Structural.frameOf` and `Named.Structural.frameOf` for every
existing constructor. SubstPlain changes no retained active payload. The subsequent
SubstActive rule substitutes into the retained active payload and projects to
that same rule; frame transport is rechecked for the expanded relation. Rewrite
keeps its full-E premise. Alpha freshness and name extrusion remain legal
because projection introduces no additional free names or nested binder names.
Variable exchange continues to use the existing Named rule.

## Action preservation and output reclosure

[SourceFrameActions](../../ExplainableCrypto/Helios/Symbolic/SourceFrameActions.lean)
proves `Reduction.frameOf` and `FreeStep.frameOf` for Extended and Named
syntax, including arbitrary structural paths at both endpoints. Plain
communication and input/output continuations erase to Nil; active constraints
and restrictions remain.

`Extended.BoundOutput.frameOf_reclose` and
`Named.BoundOutput.frameOf_reclose` prove that restricting the new output
variable in the target frame yields a frame structurally equivalent to the
source frame. The Extended result concludes in Named Structural, which has
the variable-exchange rule needed by nested Scope. No exchange rule is added
to Extended Structural. Parallel cases retain the entire shifted old context;
name Scope commutes the reclosed variable with its retained name restriction.

This does not say that a bound output leaves the public frame unchanged. Its
new handle is observable before reclosure. The result describes exactly what
happens when that fresh handle is hidden again.

## Canonical frames and active constraints

[SourceCanonicalFrameProjection](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalFrameProjection.lean)
proves that `frameEntries` and `activeFrame` are fixed by projection.
`frameProcess_frameOf` removes the projected Nil process by Structural, and
`restrictedState_frameOf` retains the canonical name prefix and complete
active frame of a scoped election state.

`Extended.Realizes.frameOf` preserves the environment constraints of any
supplied realization and gives Nil as the frame's interpreted body.
`frameOf_realizes_iff` states that the projected frame realizes Nil exactly
when the original Extended process has some realization in the same
environment. The reverse direction returns an existential body. It does not
identify that body with a previously chosen canonical election process, or
supply a fixed environment across Named alpha conversion.

## Controls and evidence

[SourceFrameProjectionSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceFrameProjectionSPOT.lean)
contains fourteen public kernel controls. Literal expected extraction retains
a private key binder and a proof's full fourth ciphertext argument. Negative
controls reject active-value erasure and a changed fourth-field plaintext.
A nonce used only in the retained ciphertext remains free; names used only in
the erased process disappear. Actual alpha, private communication and the
retained alpha-input example preserve frames. Bound output through nested
name/variable restrictions and beside an old key context recloses. Actual
complete-frame capture retains both old and fresh exports, and hiding the new
export recovers the old frame. An inconsistent active environment is rejected;
the actual canonical frame supplies a satisfying interpretation.

These are general structural proofs and independent kernel controls. No new
randomized cryptographic campaign, source-rule change, equation change, or
search-failure security inference is claimed. The reality oracle is applied-pi
frame extraction and the Figure 3 structural/action rules: restrictions and
substitutions survive process erasure, and Open-Atom exports a fresh variable.
The current finite syntax's replication, mobile-channel and arbitrary
under-prefix name-creation exclusions remain unchanged.

The subsequent [Named variable admissibility](helios-source-named-admissibility.md)
now covers exported domains, unique definitions, closed canonical targets and
free-label variable scope, including all factored action bodies. Next define
general Named equality observations and connect structural/alpha representatives
to canonical environments and process bodies.
Then complete outer voter nonce/let construction and source weak labelled
bisimilarity/symbolic secrecy. The [action factorizations](helios-source-bound-prenex.md)
and frame projection are available; that final correspondence is still open.
See the [blueprint](helios-proof-blueprint.md),
[interpretation record](helios-source-interpretation.md), and
[task list](../../task%20list.md).

Integrated verification for the frame projection checkpoint: `lake build` passes **3902 jobs**, with
**3291** nonempty standard-only and **50** axiom-free reports. The claim audit
covers **2355** public theorem entries and **98** current-status documents.
All eight changed Lean sources have current oleans; **1221** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-frame-projection-full-build.log`.
This increment adds 42 theorem audits, including fourteen public kernel controls.
Targeted controls pass 1284 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-frame-projection-verification.txt`.
