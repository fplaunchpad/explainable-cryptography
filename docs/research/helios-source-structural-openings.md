# Structural action openings and reconstruction

Status: **machine-checked** for the original source calculus. B9/B10 remain
open at 8/10 unweighted milestones. The criterion below requires actual
structural evidence for the opened bodies.

## Retain actual paths around actions

`SourcePairedOpeningReduction.Reduction.opening_binder_step` and the
`SourcePairedVisibleOpenings` FreeStep/BoundOutput counterparts strengthen the
existing paired opening construction. Their conclusions retain BinderStructural
paths on both sides of one actual Extended action. They use the already checked
structural-opening transport proof, including variable-binder commutation.
Existing `opening_step` interfaces remain derived realization projections.
There is one core construction, with no duplicated semantic proof.

Internal reduction requires an additional finite avoidance set constructed from
the prenex action endpoints' full name support; this makes the common assignment
faithful where the internal rule needs it. Free actions retain the exact complete
label. Bound output retains the channel and the entire Option-variable target.
All three retain arbitrary extra finite avoidance for the target allocation.

`SourceStructuralActionOpenings` composes these paths with the original embedded
action using Named's Struct rule. Its three `opening_named_step` theorems give
an actual Named action between the embedded chosen source opening and an actual
target opening. The resulting action is Named: BinderStructural includes
variable exchange supplied by the Named calculus.

## Reconstruct and characterize source structure

`SourceStructuralOpeningReconstruction.Opens.reclosed_freeNames_subset` proves
that reclosing an opening's allocated names introduces no new free source names.
`Opens.structural_of_binder` assumes literal openings of both original processes,
allocation lists avoiding every literal name in both processes, and an actual
BinderStructural path between the opened bodies. It concludes an original Named
structural path between the processes. The lists need not have equal length or
contain equal names.

The proof derives both actual opening/prenex paths. It adds each allocation
prefix around the other's reclosed endpoint using the free-name bound and
original unused-name rules. It then transports the body path under a common
prefix, reorders that prefix and removes the added restrictions. It never
removes a used private binder or changes a free name.

`Structural.fresh_binder_openings` proves the converse with arbitrary extra
finite avoidance. `structural_iff_fresh_binder_openings` gives the exact
characterization with both original allNames sets in the freshness conditions.
No new relation, datatype, semantic equivalence or operational rule is defined.

## Controls and evidence

Fifteen SourceStructuralOpeningSPOT controls independently pin unequal-length
unused prefixes beside a live input; actual used private-name alpha conversion;
dependent local-variable exchange; and refresh beyond both prior allocations.
The action controls retain a four-field SPK input label and echo continuation,
a scoped bound-output target with separate local/exported variables, and real
internal communication with fresh allocations on both sides.

A private channel opened onto the public spelling has an identical body but
cannot reconstruct the public process: their channel sets differ. This refutes
dropping joint allocation freshness. The inhabited unconstrained-local fixture
has the same full realizations as nil but no Named structural path to nil.
This refutes substituting SameRealizations for BinderStructural; emptiness of
the realization class does not explain that failure.

Formal oracle: the public theorem statements, kernel controls and axiom audits.
Targeted command: `lake build ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningSPOT`.
PBT gate: directed kernel controls and reuse of general structural/action
inductions; no new randomized cryptographic campaign. The historical reality
oracle is Figure 3 structural congruence, scope and action rules. Existing
trusted definitions, full E/E0 and explicit public observations are unchanged.

Integrated verification: `lake build` passes **4093 jobs**; targeted controls
pass **1394 jobs**. The current log reports **4703** nonempty standard-only and
**92** axiom-free results. The claim audit covers **3809** public theorem entries
and **132** current-status documents. All seven changed Lean sources have current
oleans; **1686** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **25** theorem audits, including **15** public kernel controls, with no new
definition or operational rule.
Log: `tmp/variable-overlap/source-structural-opening-full-build.log`.

## Remaining obligation

The criterion does not manufacture a structural body path from semantic
agreement or rigidity. Derive such paths for arbitrary reachable raw targets,
then use the criterion to recover full source presentations and matching.
General bound-output frame reconstruction and final paired bisimulation/secrecy
remain open. The checked [scoped-program capture](helios-source-scoped-capture.md)
and [execution rigidity](helios-source-rigid-execution.md) results retain their
stated scopes. See the [blueprint](helios-proof-blueprint.md).
