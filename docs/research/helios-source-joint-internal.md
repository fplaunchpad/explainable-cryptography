# Internal transitions preserve joint restricted states

Current frontier: [coordinated phases](helios-source-coordinated-phases.md) now
classify arbitrary inputs after common freshening and retain shared coordinates
through later internal traces and bound outputs. Arbitrary raw partner action
construction and final secrecy remain open. Earlier limits below describe
their historical checkpoint.

Current frontier: [joint visible closure](helios-source-joint-visible.md) now
retains public-input and full bound-output targets, identifies output phases
and constructs a common fresh input policy in both worlds. Input-stage matching
across those coordinates, arbitrary action construction and final secrecy
remain open. Earlier limits below describe their historical checkpoint.

Status: **machine-checked** internal closure of JointOpening and election
PhaseJointOpening, including finite raw internal traces. Both actual scoped
processes remain in the relation, with a nonempty complete realization class.
Visible closure and final weak labelled bisimilarity/symbolic secrecy remain
unproved. B9/B10 stay incomplete at 8/10 unweighted milestones (80%).

## Paired endpoint permutations

[SourcePairedCanonicalPermutations](../../ExplainableCrypto/Helios/Symbolic/SourcePairedCanonicalPermutations.lean)
proves `Named.Opens.prefix_permutations_pair`. Starting from an opening of one
Extended body beneath a restriction prefix, it constructs an opening of a second
body beneath the same prefix and with the same allocation list. Freshness avoids
the union of both bodies' name supports. A faithful assignment on that union
extends to base/channel permutations that describe both opened endpoints.

This endpoint union matters: permutations obtained solely for the first body
need not agree with the second body's assignment on newly used names. The
proof explicitly retains the second opening and its actual restriction prefix.
It does not infer a source Structural presentation from SameRealizations.

## Generic internal closure

[SourceJointOpeningInternal](../../ExplainableCrypto/Helios/Symbolic/SourceJointOpeningInternal.lean)
proves `Named.JointOpening.internal`. Given an actual raw Reduction and a joint
relation to `restrictedState hidden ⟨φ,p⟩`, the conclusion is JointOpening of the
actual raw target with `restrictedState hidden ⟨φ,q⟩`. The explicit generic
premise says every actual Tau target of p is EvalEq to q.

The proof refreshes both source openings against the target free-name union,
the raw reduction's required names and both canonical endpoint supports.
`Reduction.opening_step` supplies an actual opened raw action and full source/
target comparisons. The paired canonical opening supplies one permutation for
both full frame/body states. Deterministic complete target-class closure then
compares the actual target openings. A canonical target realization gives the
required nonvacuity witness. Both allocation lists avoid both target free-name
sets, so the result can be refreshed for another transition.

`JointOpening.tau` constructs an actual canonical Tau in the original
coordinates from the actual raw action. Internal closure adds no action or
structural rule; it retains the restriction witness that the earlier body
invariant discarded.

## Election phases and traces

[SourceElectionJointInvariant](../../ExplainableCrypto/Helios/Symbolic/SourceElectionJointInvariant.lean)
proves `source_joint_internal_next`. Channel freshness and an in-range phase
supply actual residual determinism and completeness. The generic determinism
premise is discharged, and the conclusion includes an actual next phase, its
internal Step, exact equality of handle counts and the joint relation to the
full next restricted source state.

`PhaseJointOpening` records the relation with explicit transport between the
raw handle domain and the phase handle domain. It holds canonically, survives
all source Structural changes and implies the earlier PhaseOpening body
invariant. `.internal_trace` handles every finite sequence of actual Named
internal reductions from a reached phase. It constructs a reached next phase,
a corresponding finite internal stage trace and the stronger relation on the
unchanged final raw target. No intermediate raw target needs a canonical
Structural presentation.

The phase relation retains exact free-channel support. Its free/bound channel
publicness theorems therefore apply after any such trace. These are necessary
policy consequences, not converse constructions of source actions or complete
static equivalence of arbitrary raw frames.

## Controls and evidence

[SourceJointInternalSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceJointInternalSPOT.lean)
has 19 public kernel controls. A then transition ends in a raw target with an
extra parallel zero; joint closure retains both its frame/body and private
channel policy. The else branch is covered separately. Private communication
transfers a full SPK payload to a public output and leaves another private
output blocked. Wrong branch/channel support and wrong old frame values are
rejected. Competing branch/communication outcomes refute dropping generic
determinism, and the prior private/public pair still refutes using the old
body invariant as a substitute.

An actual two-step trustee trace retains PhaseJointOpening in either vote
world. The final two controls cover arbitrary finite raw internal traces from
a reached sendTally phase and arbitrary target processes: every private-channel
input and output remains blocked. Expected messages, names, branches and
phase fixtures are independently specified.

The gate uses directed kernel controls and general proofs, with no new random
cryptographic campaign or security inference from search failure. The local
Cortier–Smyth Figures 2–3 give Comm/Then/Else, restriction and Structural closure.
Full E/E0, all cryptographic fields and explicit source/public observations
remain unchanged. PhaseJointOpening is a proof invariant, not a new source rule.

Integrated verification: `lake build` passes **4047 jobs**. The log reports
**4360** nonempty standard-only and **91** axiom-free results. The claim audit
covers **3465** public theorem entries and **121** current-status documents.
All six changed Lean sources have current oleans; **1555** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **32** theorem audits,
including **19** public kernel controls, and one phase invariant definition.
The targeted control build passes **1419 jobs**.
Build log: `tmp/variable-overlap/source-joint-internal-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-joint-internal-verification.txt`.

Remaining: visible closure of JointOpening, coherent public input-recipe and
phase alignment under alpha renaming, existing-handle output closure,
output-frame Structural presentation, action construction in arbitrary related
raw representatives and the final weak labelled bisimulation/secrecy theorem.
See the [blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and [task list.md](../../task%20list.md).
