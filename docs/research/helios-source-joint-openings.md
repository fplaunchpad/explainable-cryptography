# Joint fresh openings and private channels

Current follow-up: [Named execution rigidity](helios-source-rigid-execution.md)
now preserves the necessary invariant through all original Named actions and
finite executions with bijective handle reindexing. The cyclic joint family is
excluded from executions starting at canonical election states. Sufficient
reachable reconstruction and full secrecy remain unproved.

Current update: [binder rigidity](helios-source-binder-rigidity.md) now proves
full Named.Structural separation of the cyclic joint pair and excludes all its
ground frame presentations/StaticEq partners. Structural opening comparison is
stronger, and Extended bound-output rigidity is checked. Earlier statements
leaving these facts open below are historical; reconstruction sufficiency remains open.

Current update: [local rigidity](helios-source-local-rigidity.md) refutes the
Extended normalization implication from WellFormed/nonempty full class alone.
The counterexample also has an embedded joint opening; Named.Structural
separation and a sufficient reconstruction invariant remain open.

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

Current frontier: [joint internal closure](helios-source-joint-internal.md) now
retains the actual restricted canonical state through raw internal steps and
finite internal traces. Joint visible closure, the source-action converse and
final secrecy remain open. Earlier boundary statements below describe their
historical checkpoint.

Status: **machine-checked** coherent refresh, Structural preservation, full-body
invariant implication and free-channel preservation for JointOpening.
The private/public counterexample to HasCanonicalOpening is excluded.
Operational closure and final weak labelled bisimilarity/symbolic secrecy remain
unproved. B9/B10 are incomplete: 8/10 unweighted milestones (80%).

## Definition and nonvacuity

[SourceJointOpening](../../ExplainableCrypto/Helios/Symbolic/SourceJointOpening.lean)
defines `Named.JointOpening a d` by openings of both actual Named processes.
Their allocation lists avoid the union of both free-name sets; their complete
Extended bodies have SameRealizations for every environment and process body;
and at least one such realization exists. Lists can differ, so an unused
restriction can be added or removed. Canonical full frames have a realization
and satisfy the relation with themselves. General inconsistent processes do not.

The existence condition is essential. The controls constrain one handle to
both distinct names 40 and 41. Neither that process nor its parallel composition
with an output has a realization. Their empty realization classes are equal,
but their channel sets differ. `nonvacuity_rejects_inconsistent_self` checks that
the new relation excludes even the reflexive inconsistent pair. No unrestricted
reflexivity or transitivity theorem is asserted.

## Coherent refresh and structural preservation

`JointOpening.fresh` constructs new openings avoiding any requested finite set,
in addition to both free-name sets. It applies the same base/channel value
permutations to both openings, using their combined allocation list, and fixes
both source free-name sets. Full realization equality and the concrete witness
move together. The original sources are unchanged.

The relation is symmetric. `structural_left` and `structural_right` preserve it
through every original source Structural derivation by transporting fresh
openings. `Structural.jointOpening` relates any Structural representative of
an actual restricted canonical state to that state. No equality of allocation
lists or binder spellings is required. `JointOpening.interprets` gives a common
complete interpretation of the two actual processes.

## Channel policy

[SourceRealizationChannels](../../ExplainableCrypto/Helios/Symbolic/SourceRealizationChannels.lean)
proves exact channel preservation through ParEq, full process EquivE and EvalEq.
`Extended.Realizes.channels` retains all channels, including both branches and
waiting continuations. A nonempty SameRealizations class therefore determines
the complete opened channel set.

[SourceJointOpeningPolicy](../../ExplainableCrypto/Helios/Symbolic/SourceJointOpeningPolicy.lean)
proves `JointOpening.channels`: the actual Named processes have equal free
channel sets. For each tested channel, refresh avoids that channel and all
names of both sources. Existing structural opening derivations and restriction
support then reflect the opened equality back to the actual processes.

For a restricted canonical partner, `hasCanonicalOpening` recovers the previous
full-body invariant. `free_channel_public` and `bound_channel_public` show that
actual raw free/bound actions use channels outside the canonical private set.
The corresponding private-channel blocking theorems cover all raw targets and
all original structural action paths. The proofs do not assume publicness as
an extra callback.

This is channel policy evidence. It does not yet establish public input-recipe
alignment under base-name permutations, operational closure of JointOpening,
a converse construction of source actions, or Structural frame presentation.
Equal free channel sets alone are not asserted to characterize the relation.

## Controls and verification

[SourceJointOpeningSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceJointOpeningSPOT.lean)
has 16 public kernel controls: realizable canonical/public cases; rejection of
the restricted/public pair in both orientations; strict strengthening of the old
body invariant; actual alpha renaming; blocked private output; unused channel
restriction; refresh avoiding both old spellings; inconsistent active equations;
empty classes with different channels; and full continuation support.
Expected literal names and channel sets are independently specified. The gate
uses directed controls and general proofs, with no new randomized crypto
campaign or inference from failed attack search. Cortier–Smyth Figures 2–3
restriction, alpha and Open rules supply the model reference. Full E/E0,
all cryptographic fields and source/public observation semantics are unchanged.
The new definition is a candidate proof relation, not a new source rule.

Integrated verification: `lake build` passes **4043 jobs**. The log reports
**4329** nonempty standard-only and **90** axiom-free results. The claim audit
covers **3433** public theorem entries and **120** current-status documents.
All six changed Lean sources have current oleans; **1545** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **35** theorem audits,
including **16** public kernel controls, and one candidate relation definition.
The targeted control build passes **1415 jobs**.
Build log: `tmp/variable-overlap/source-joint-opening-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-joint-opening-verification.txt`.

Next: retain both canonical/raw opening witnesses through actual transitions;
prove input-recipe and phase alignment, the required source-action converse,
existing-handle output closure and output-frame Structural presentation; then
establish the final weak labelled bisimulation and secrecy theorem. Earlier
HasCanonicalOpening internal trace/input/bound-output preservation does not
by itself prove closure of this stronger relation. See the
[blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md) and
[task list.md](../../task%20list.md).
