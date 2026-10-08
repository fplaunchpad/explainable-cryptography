# Rigidity throughout Named executions

Current follow-up: [dependent program captures](helios-source-program-capture.md)
now reconstructs actual Scope targets for every finite existing TermProgram,
including dependent local definitions and full Named frame presentations.
General extraction through reachable structural representatives remains open.

Current follow-up: [recipe capture reconstruction](helios-source-recipe-capture.md)
now gives full provider-context substitution and actual ground presentations
for explicit fresh recipe-valued captures. Extracting that form from arbitrary
reachable representatives, and final secrecy, remain open.

Status: **machine-checked** necessary invariant of all original Named action
kinds and their finite execution closure. The cyclic joint semantic partner is
unreachable from canonical election states under this closure. B9/B10 remain
open at 8/10 unweighted milestones; symbolic secrecy remains unproved.

## Actual allocations and actions

`Named.LocallyRigid` quantifies over every assignment, actual name opening and
complete variable environment. Its body uses Extended.Rigid, which retains
uniqueness modulo full E for each remaining local variable. Name choices remain
explicit outside the local-variable predicate. This avoids the invalid shortcut
of treating existential Named.Models choices as one shared assignment. The
predicate allows inconsistent environments, where rigidity is vacuous; it does
not assert existence of interpretations or a complete exported domain.

`SourceNamedLocalRigidity` proves:

- `Opens.of_frameOf` reconstructs an opening of the full process with exactly
  the allocation of any frame opening. Together with Opens.frameOf this gives
  `locallyRigid_frameOf` in both directions.
- `Structural.locallyRigid` uses the stronger actual binder-structural opening
  transport. Arbitrary name/variable scope, alpha and mixed binder exchange
  are covered by the original structural induction.
- `Reduction.locallyRigid` and `FreeStep.locallyRigid` preserve and reflect the
  invariant through complete frame projection. Both free label kinds are covered.
- `BoundOutput.locallyRigid_reclose` preserves it exactly after hiding the newly
  exported handle. `BoundOutput.locallyRigid` preserves all remaining locals
  forward. `LocallyRigid.newVar_body` decomposes any target environment into
  old values and the exported value; it assumes no satisfying target assignment.
- `LocallyRigid.rename` handles every bijective variable relabelling, including
  outputHandle. Embedding, sorted name restriction and complete canonical frame
  presentation give initial invariant witnesses.

## Finite reachable states

`Named.Execution` is a finite closure of original Structural, Reduction,
FreeStep and BoundOutput derivations, with reflexivity, transitivity and explicit
bijective handle reindexing. Its endpoints may have different variable types.
The reindex constructor is a coordinate change, not a protocol transition.
Only an original bound output adds a public handle. The closure forgets labels
for this invariant argument; it is not the final labelled simulation relation.

`Execution.locallyRigid` preserves the invariant across every finite mixture.
`Execution.from_presented` starts with any actual ground frame presentation;
`Execution.from_canonical` starts with a complete source state. The generic
`canonical_no_execution_to_cycle` excludes the entire cyclic family beside
arbitrary complete frames and plain bodies, even with intermediate outputs and
handle relabellings.

`source_coordinated_execution_rigid` and
`source_coordinated_no_execution_to_cycle` instantiate these results at every
mapped canonical election phase, for explicit base/channel permutations. No
freshness or phase-reachability premise is needed for this necessary invariant.
This does not remove those premises from the protocol matching/secrecy goal.

## Controls and boundary

Twenty public controls in SourceRigidExecutionSPOT retain actual sorted-name
and variable-scoped output, followed by input on the exported handle. A chosen
opening fixes the private local to 50 and the public capture to 41; supplying 50
as the capture is rejected. The complete canonical publication uses actual
bound output, Option-to-Fin reindexing and a structural path to the full emitted
frame. Actual private communication progresses under its channel restriction.

The cyclic process still has its semantic JointOpening partner but no execution
from the canonical live frame. A different cyclic source can perform an actual
unconstrained export and leave a rigid target, so reverse output preservation
is refuted. Reclosing that target retains the uniqueness failure. These controls
exclude stuckness, collapsed handle domains and a mistaken two-way output rule.

The formal oracle is Lean rule induction and directed kernel controls. The
reality oracle is the original Figure 3 structural/Scope/Open-Atom rules and
complete frame projection. Full E/E0, SPK's fourth field, E5 structured keys,
E6 full ciphertexts and explicit public observations are unchanged. No new
randomized cryptographic campaign or operational rule is claimed.

Integrated verification: `lake build` passes **4081 jobs**; targeted controls
pass **1397 jobs**. The current log reports **4588** nonempty standard-only and
**91** axiom-free results. The claim audit covers **3693** public theorem entries
and **128** current-status documents. All five changed Lean sources have current
oleans; **1649** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **42** theorem audits, including **20** public kernel controls, and two
auxiliary definitions (LocallyRigid and the original-action execution closure).
Log: `tmp/variable-overlap/source-rigid-execution-full-build.log`.

## Remaining obligation

Maintain enough reachable structural/frame information to reconstruct canonical
presentations and construct matching actions from arbitrary raw counterparts.
LocallyRigid is necessary; sufficiency of rigidity combined with the other
reachable invariants is unproved. The present theorem excludes the known cycle
but does not normalize a general reachable target. Raw bound-output frame
presentation, paired weak labelled bisimulation and final secrecy remain open.
The [old-handle election case](helios-source-publication-separation.md) remains
closed.

See the [blueprint](helios-proof-blueprint.md),
[task list](../../task%20list.md) and [results ledger](helios-results.md).
