# Atomic output, fresh exports and active frames

B9 now derives public output from Out-Atom and Open-Atom in the explicit
variable/active source fragment. Arbitrary emitted terms become full active
substitutions under fresh exported variables. The old frame and entire parallel
continuation survive. An explicit bijection maps the fresh variable to the next
canonical handle, after which the target is structurally equivalent to the
actual extended public frame. Every evaluated scoped output has this derivation.
These are machine-checked supporting results. The full source converse, name
scope/alpha, source well-formedness and final bisimilarity remain open; B9/B10
stay at 8/10 milestones (80%, unweighted).

## Free and bound source labels

[SourceAtomicLabels.lean](../../ExplainableCrypto/Helios/Symbolic/SourceAtomicLabels.lean)
defines free input/output labels and separate bound variable outputs. Free
input carries a term; free output carries a base variable. `FreeStep` has In,
Out-Atom, variable Scope, parallel contexts and structural closure. An input
can cross variable scope only with a shifted term that does not mention the
restricted binder; a free output can cross it only through an old variable.

`BoundOutput` implements Open-Atom, variable Scope, Par and Struct. Open-Atom
removes the output variable's restriction. Its inequality with the channel is
guaranteed by the separate base-variable and static-channel-name sorts. Parallel
contexts shift every old variable under Some, ensuring freshness. Crossing an
existing variable restriction swaps the two fresh binder positions: the old
local remains restricted and the new output becomes exported. The swap is
proved involutive, so it cannot merge variables.

These rules cover variable-labelled actions in the existing finite static-
channel fragment. Name restriction and name outputs, arbitrary channel variables,
full source alpha-equivalence and the extended operational converse are still
separate obligations. The recipe-input bridge now derives input beside actual
active frames using In and explicit active Subst, retaining the literal label.

## Full-message output and export preservation

[SourceAtomicOutput.lean](../../ExplainableCrypto/Helios/Symbolic/SourceAtomicOutput.lean)
defines `capture m p` as a fresh active substitution containing the complete
shifted term m, in parallel with the shifted continuation p. `message_output`
factors the message through the previously proved active-let equivalence, uses
Out-Atom on its fresh variable, then Open-Atom to export it. No arbitrary-message
output is introduced as a primitive rule.

Free labelled steps preserve exported variables. Bound outputs preserve every
old export through all variable scope, parallel and structural rules. The actual
derived capture also exports its fresh variable. The latter is stated for the
derived capture rather than assumed for arbitrary raw syntax, since raw extended
syntax also contains ill-formed source expressions. The separate variable
well-formedness invariant and preservation from actual canonical frame states
are now proved.
A whole extended context can remain beside the output and retains all its old
variables and active substitutions.

## Source frames and canonical handles

[SourceExtendedRenaming.lean](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedRenaming.lean)
proves identity/composition of free-variable renaming through extended syntax,
including active domains and restrictions. Ground payload/process embeddings
commute with renaming without changing names or introducing free variables.
These syntax laws are not a proof of full source name alpha-equivalence.

[SourceActiveFrames.lean](../../ExplainableCrypto/Helios/Symbolic/SourceActiveFrames.lean)
represents every public frame as a parallel collection of active substitutions,
with its full ground values. `activeFrame_extend` identifies the new binding and
all retained bindings exactly. `outputHandle` reuses Mathlib's bijection from
`Option (Fin h)` to `Fin (h+1)` sending None to the last handle and Some i to
castSucc i. Injectivity prevents the fresh export from aliasing an old handle.

`frame_output_capture` renames the actual bound-output target by that bijection.
Only parallel associativity and commutativity are then needed to obtain the
source frame representation of `φ.extend m` beside the complete continuation.
The payload is neither normalized nor replaced. This is a literal syntax/
structural capture result, not an assertion that arbitrary source binder
renaming or name restriction has already been handled.

[SourceOutputDerivation.lean](../../ExplainableCrypto/Helios/Symbolic/SourceOutputDerivation.lean)
lifts the atomic derivation through all active parallel positions and ParEq.
`visible_output_derivable` covers every evaluated visible output, and
`frame_visible_output_derivable` retains its actual public active frame.
`scoped_output_derivable` connects every evaluated scoped output to this source
bound output and to the exact target frame after canonical handle renaming.
It starts from an already-public scoped step; the wrapper's fixed
name-restriction filter is not derived from source name-scope rules.

## Controls and remaining bridge

Eleven controls in
[SourceAtomicOutputSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceAtomicOutputSPOT.lean)
retain a deliberately visible literal secret, a compound payload with an old
variable, and an output crossing an enclosing local variable restriction.
The crossing really exports the new variable. Dropping an old exported binding
is impossible. Concrete handle mapping gives 2 for the new binder and 0/1 for
the old handles, and the new handle cannot alias either old one. An independently
written key-plus-secret active frame agrees with the capture; redacting its
new value gives different syntax. The actual first election publication has
a bound-output derivation with its whole residual context.

The redaction control compares explicit frame syntax; it does not claim a
converse theorem excluding every arbitrary source output derivation. Export
preservation concerns domains, not equality of all frame values. The secret
fixture validates that the model exposes leaks; it is not an election attack.
These are general structural proofs and kernel controls, with no new randomized
security campaign or evidence from search failure.

Public recipe input and internal steps now derive beside actual active frames.
Variable well-formedness is now certified for actual frames, ground lets, raw
captures and their targets. Next connect outer voter construction, add name
restriction/scope and source alpha-equivalence, and prove the full operational
converse.
Then combine the actual observations and transitions into source weak labelled
bisimilarity and full symbolic secrecy. See the [active internal bridge](helios-source-active.md),
[visible correspondence](helios-source-visible.md), maintained
[blueprint](helios-proof-blueprint.md) and [task list](../../task%20list.md).

Integrated verification for the atomic-output checkpoint: `lake build` passes **3822 jobs**, with
**2753** nonempty standard-only and **44** axiom-free reports. The claim audit
covers **1811** public theorem entries and **85** current-status documents.
All eight changed Lean sources have current oleans; **1061** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-atomic-output-full-build.log`. This
increment adds 35 theorem audits, including eleven kernel controls, and eleven
definition checks. Targeted controls pass 1200 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-atomic-output-verification.txt`.
