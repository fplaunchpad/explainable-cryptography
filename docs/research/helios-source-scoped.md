# Scoped public actions and fresh output handles

B9 now has ground input/output rules modulo parallel structure, an exact
active-prefix/context characterization, and an evaluated public-frame wrapper.
Its public input labels carry recipes; outputs bind a fresh frame handle and
retain the full emitted value. A fixed outer private-channel set blocks both
visible directions while permitting internal handshakes. The election's four
publication prefixes and next-voter input have checked realizations, and the
retained rejected trustee has no wrapper step. These are machine-checked
supporting results. [Exact visible correspondence and frame capture](helios-source-visible.md)
are now checked too. The extended-source scope and substitution bridge remains
open; B9/B10 stay at 8/10 milestones (80%, unweighted).

## Visible rules and public labels

[SourceVisibleSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleSyntax.lean)
defines direct ground input/output events and rules, parallel contexts, and
closure by ParEq. Ground output payload events are an internal presentation of
the emitted value. They are not the public output labels used by the wrapper.
`PrimitiveVisible` has just the input and output prefix rules.

[SourceVisibleReduction.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleReduction.lean)
proves `visible_iff_threads` in both directions: one active prefix takes its
input or output action and the real parallel context is unchanged. Both the
full event and payload are preserved. Prefix inversion rules identify the input
or output in the actual thread multiset. In particular, structural closure
cannot expose an action below another input, output or conditional.

[SourceScopedSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceScopedSyntax.lean)
defines `ScopedState restricted handles` with an actual public frame and ground
finite process. `PublicEvent` is indexed by the before/after handle counts.
Tau and input keep the count; output has type `handles → handles+1` and binds
the canonical next handle. It carries its channel, not the ground output value.
Input carries a recipe over exactly the current handle domain.

`ScopedStep` interprets an input recipe in the state's frame and substitutes the
result into the receiving process. It requires the recipe's literal names to
be public. An output appends its exact value to the frame; it does not require
the value itself to avoid restricted names. Thus encrypted ballots, proofs and
partials retain all their fields, and a process that outputs a secret directly
really does expose it through the new public handle.

## Fixed outer restriction and frame preservation

The historical hidden channels are `Channels.privateChannels`: the two honest
voter channels and the trustee channel. Both public input and public output
rules require their channel to be outside this set. Tau has no such requirement,
so private communication remains possible inside the process.

[SourceScopedActions.lean](../../ExplainableCrypto/Helios/Symbolic/SourceScopedActions.lean)
proves that separated channel assignments leave broadcast public and make voter
channel `i` public exactly for `i ≥ 2`. It proves exact Tau/input/output inversion
for the wrapper. Inputs and Tau preserve the existing frame. An output's fresh
handle differs from every old handle, exposes the exact emitted value, and
preserves the values of all previous recipes under their standard lifting.
Neither freshness nor old-value preservation assumes that the payload is a new
or distinct term.

This is a fixed outer restriction on an evaluated representation. Deriving it
from arbitrary source restriction/scope structure remains necessary. Likewise,
the fresh-handle frame extension still needs its correspondence to source
Out-Atom/Open-Atom and active substitutions, including arbitrary binder renaming.
These obligations are not hidden as premises in ScopedStep or marked complete.

## Election steps and controls

[SourceVisibleElection.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleElection.lean)
realizes the first honest relay, second honest relay, partial publication and
result publication with their actual source payload expressions. The second
relay continues to the correct next-input/tally boundary. A next-voter input
reaches the actual pending guard and leaves its acceptance decision for a later
Tau. `residual_scoped_input` uses the actual initial three-handle frame and checks
both the public recipe and the correct public voter channel.

`rejected_no_scoped_step` rules out every wrapper event from a rejected residual
for any public frame. Internal quiescence is reused, visible output is absent,
and its only input is on the restricted trustee channel. The trustee remains in
the process syntax; no erasure is used to establish stopping.

Eleven kernel controls in
[SourceScopedSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceScopedSPOT.lean)
check a public input through a handle whose value contains a restricted atom,
rejection of a literal restricted-name recipe, blocking both private visible
directions, and preserving a real private handshake. A new output handle is
fresh and preserves all old recipes. A deliberately leaking process exports
its secret exactly, while a mutant that replaces that output by bottom fails
the transition rules. This is a model control, not a leak in the historical
election. Sequential outputs cannot be reordered. Actual election input reaches
its pending check and actual rejection has no wrapper event.

These are structural and frame-rule proofs with kernel controls, not a new
randomized security campaign. Elaboration issues concerned a dependent output
continuation name and list-map expansion in the input continuation; no claim was
weakened. No privacy conclusion is inferred from private-channel blocking alone.

Full visible transition classification and exact captured source views are now
checked in both directions. Atomic Comm and active lets now derive evaluated
internal steps in the variable/active fragment. Atomic bound output now derives
scoped outputs with the exact full active frame. Recipe inputs and internal
steps now also derive beside actual active frames. Next establish the full source
converse, name restrictions/scope, outer voter construction and name alpha-
equivalence. Variable well-formedness is now certified for the actual frame
states, fresh ground lets, raw captures and all their step targets. Finally connect the observations and assemble source
weak labelled bisimilarity and the full symbolic secrecy theorem. Canonical
handle freshness alone does not discharge arbitrary source output-binder naming.

Integrated verification for the scoped-rule checkpoint: `lake build` passes **3804 jobs**, with
**2666** nonempty standard-only and **41** axiom-free reports. The claim audit
covers **1721** public theorem entries and **82** current-status documents.
All nine changed Lean sources have current oleans; **1026** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-scoped-full-build.log`. This increment
adds 40 theorem audits, including eleven kernel controls, and ten definition
checks. Targeted controls pass 1177 jobs.
