# Local solutions and the normalization boundary

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

Status: **refuted** — WellFormed and a nonempty full realization class do not
imply an Extended Structural presentation. The separating invariant and its
preservation theorems are **machine-checked**. B9/B10 remain open at 8/10
unweighted milestones (80%); the final secrecy theorem is not refuted or proved
by this result.

The restricted process `νx.{x/x}` admits every ground value for its local x.
It is closed and has exactly one active definition. Its full realization class
is the same as nil's: existential interpretation hides the unused local value.
Nevertheless, it cannot normalize to nil using the original Extended Structural
rules. The proof separates the two processes by uniqueness of local solutions
modulo full E.

## Checked invariant

`Extended.Rigid a env` requires every local variable's value to be uniquely
determined modulo E whenever the relevant complete constraints hold. A parallel
component imposes its rigidity requirement only when both components satisfy
their constraints. A restricted variable requires uniqueness of its possible
values and rigidity of its body under each satisfying extension. Inconsistent
constraints are vacuously rigid; existence is a separate property.

`SourceLocalRigidity` proves renaming and frame-projection compatibility,
source scope extrusion, and `Structural.rigid` for every original Extended
structural rule. Alias is rigid because the new value equals the supplied outer
term. Subst and Rewrite preserve the constraints. The invariant is a proof
definition and adds no operational rule or source admissibility restriction.

`SourceRigidityPreservation` proves `Reduction.rigid` and `FreeStep.rigid` using
the existing complete frame-projection theorems. Canonical active frames and
frame/process states are rigid in every environment. Consequently,
`Structural.rigid_of_frame_target` gives a necessary condition for a genuine
Extended normalization to a canonical frame/process.

## Counterexample and controls

`SourceRigidityBoundary` proves the counterexample for arbitrary outer variable
types, frames and bodies:

- `unconstrained_local_sameRealizations` equates the local self-reference's
  entire realization class with nil's, for all environments and bodies.
- `unconstrained_local_not_rigid` uses distinct names 40 and 41 as two solutions.
- `frame_with_unconstrained_local_sameRealizations` retains the entire class
  beside any canonical frame/process, including every old public value.
- `frame_with_unconstrained_local_wellFormed` discharges current scope and
  unique-definition conditions.
- `frame_with_unconstrained_local_not_structural` excludes Extended normalization
  to that canonical partner.
- `frame_with_unconstrained_local_joint` proves the corresponding embedded
  Named.JointOpening relation, including nonvacuity.

`SourceLocalRigiditySPOT` has thirteen public kernel controls. An independent
ground alias actually normalizes via Alias and is rigid. The cycle is well
formed, shares an inhabited class with nil, and cannot normalize to it. The
universal conjecture with both endpoints well formed and an explicitly nonempty
class is refuted. A real conditional step preserves a ground alias's rigidity.
The counterexample also appears beside a one-handle frame and an input/output
body; an actual public input executes there. Thus no claim that the cycle
forces immediate stuckness is used.

The reality oracle is Figure 3 Alias/Subst/Rewrite. Alias supplies a term from
the outer context, independent of its new local variable. The paper's separate
no-cycle condition on its infinite enriched frame is not promoted to an
unstated general source admissibility axiom. Full E/E0 and public observations
remain unchanged. Directed kernel controls and a general rule induction provide
the evidence; no randomized cryptographic campaign is claimed.

Integrated verification: `lake build` passes **4071 jobs**. The current log
reports **4504** nonempty standard-only and **91** axiom-free results. The claim
audit covers **3609** public theorem entries and **126** current-status documents.
All six changed Lean sources have current oleans; **1624** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **30** theorem audits,
including **13** public kernel controls, and one auxiliary proof definition.
The targeted control build passes **1210 jobs**.
Build log: `tmp/variable-overlap/source-local-rigidity-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-local-rigidity-verification.txt`.

## Effect on the proof blueprint

Do not retry the refuted implication with only WellFormed, nonvacuity or
SameRealizations added as premises. The current JointOpening relation also
admits the embedded counterexample, but the proved non-Structural result is
for Extended.Structural only. Named.Structural includes additional name and
variable-binder rules; its separating invariant is still to be proved.

Rigidity is necessary for Extended canonical presentation; sufficiency is open.
Preservation through bound output and name-scoped fresh openings is also open.
This increment does not refute action matching, prove protocol insecurity or
establish that the cycle is reachable from the election. A stronger reachable
invariant and a proved reconstruction theorem are required for the remaining
raw action and bound-output frame obligations, followed by final bisimulation.

See the [blueprint](helios-proof-blueprint.md),
[publication separation](helios-source-publication-separation.md),
[task list](../../task%20list.md) and [results ledger](helios-results.md).
