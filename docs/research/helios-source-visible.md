# Exact visible election correspondence and captured views

B9 now classifies every public input and output of an in-range literal election
residual in the evaluated frame wrapper. Outputs are exactly the four historical
publications, with their full messages; the only input is the next extra voter.
Targets preserve the prescribed continuation modulo parallel structure. Each
publication captures exactly the next source frame, whose observations inherit
B7/B8 at reachable stages. These are machine-checked supporting results.
B9/B10 remain incomplete at 8/10 milestones (80%, unweighted): the extended-source
active-substitution/scope bridge and full symbolic secrecy theorem remain open.

## Prefixes and arbitrary targets

[SourceVisibleInversion.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleInversion.lean)
extracts the entire active continuation and untouched parallel context from a
visible input or output. If that active continuation is unique, multiset
cancellation proves that any two targets are parallel-equivalent. Uniqueness
concerns the whole continuation, not just a shared channel or payload.

[SourcePublicationSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourcePublicationSyntax.lean)
defines `Publication`, a value-retaining adapter for the four existing stage
output constructors. Each adapter supplies a stage step and the actual visible
source output. Every stage output has such an adapter; no new stage transition
is introduced.

[SourcePublicOutputPrefixes.lean](../../ExplainableCrypto/Helios/Symbolic/SourcePublicOutputPrefixes.lean)
and [SourcePublicInputPrefixes.lean](../../ExplainableCrypto/Helios/Symbolic/SourcePublicInputPrefixes.lean)
classify all twelve residual forms. Public outputs are precisely the first
honest relay, second honest relay, partial tuple and result tuple. Only the
input phase exposes an input, on voter channel `history.length+2`. In both
cases the full active continuation is unique and every target agrees with the
prescribed residual modulo `Agent.ParEq`. Conversely that residual, or any
parallel-equivalent target, is possible with the stated action.

These raw classifications assume the phase is in range and the event channel
is outside `Channels.privateChannels`. They do not assume acceptance of a
pending input. The range premise matters: an exhausted collection unfolds to a
tally send instead of an input. Sequential and guarded prefixes cannot become
active through parallel rearrangement.

## Exact frames and typed wrapper actions

[SourceCapturedViews.lean](../../ExplainableCrypto/Helios/Symbolic/SourceCapturedViews.lean)
defines `sourceView` and `sourceState` at the stage-dependent handle domain.
The first views contain the public key and then the actual honest ballots;
partial/result views retain the literal emitted expressions, including tuple
projections. `Publication.capture` proves literal equality between frame
extension by the actual message and the next view. Heterogeneous equality keeps
the dependent handle indices explicit. Both zero and positive extra-voter
counts are covered at the second publication.

`source_view_pointwise` relates every source view to the existing stage view
modulo E. `reachable_source_view_staticEq` then transfers B7/B8 to actual source
observations at every reachable stage, for fresh names and arbitrary valid
ground candidate substitutions. The theorem uses reachability to discharge
public-history and accepted-sequence premises where partials/results occur.

[SourceVisibleCorrespondence.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleCorrespondence.lean)
proves exact wrapper input/output characterizations under `Channels.Fresh` and
in-range control. A public input recipe is over the current handle domain;
inversion proves this must be the three-handle input phase. The input evaluates
that recipe and leaves both the existing frame and the pending guard intact.
An output labels only the public channel and fresh handle, while its captured
frame contains the full emitted value. `source_scoped_output_capture` connects
any such target to the stage output and exact next source view.

## Controls, evidence and remaining scope

Nine kernel controls in
[SourceVisibleCorrespondenceSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleCorrespondenceSPOT.lean)
check the first publication's retained key and actual ballot, the second
publication's zero-extra-voter boundary, and a real input retaining an unrelated
waiting thread. Negative controls reject skipping to a later voter, input while
a guard is pending, ballot redaction, overwriting the old key handle, and dropping
the waiting thread. Initial source-frame static equivalence is also instantiated.
The expectations come from the literal output order, channel numbers, handle
contents and parallel multiplicity. These structural proofs and controls are
not a new randomized security campaign.

This closes public visible classification and captured-frame agreement for the
evaluated wrapper. Deriving the wrapper from the historical extended calculus
now has an atomic-Comm/active-let derivation of evaluated internal steps in a
variable/active fragment. Atomic bound outputs now derive scoped outputs beside
actual active frames with exact capture after fresh-handle renaming. The full
operational converse, name restriction/scope, arbitrary source alpha-equivalence
and outer voter construction remain required. Variable closedness and unique
definitions are now proved for actual frame states and their targets. Recipe inputs now derive with
their original labels and exact target beside the actual active frame. The current finite Agent has static channels and no internal restriction
or replication. Fixed outer filtering and canonical handle freshness do not
by themselves prove that source correspondence. Next combine that derivation
with [internal correspondence](helios-source-internal.md), the reached-frame
observations and [stage matching](helios-process-stages.md), then assemble source
weak labelled bisimilarity and full secrecy. The
[blueprint](helios-proof-blueprint.md) and [task list](../../task%20list.md)
retain B9/B10 as open.

Integrated verification for the visible-correspondence checkpoint: `lake build` passes **3811 jobs**, with
**2692** nonempty standard-only and **42** axiom-free reports. The claim audit
covers **1748** public theorem entries and **83** current-status documents.
All nine changed Lean sources have current oleans; **1040** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-visible-full-build.log`. This increment
adds 27 theorem audits, including nine kernel controls, and three definition
checks. Targeted controls pass 1184 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-visible-verification.txt`.
