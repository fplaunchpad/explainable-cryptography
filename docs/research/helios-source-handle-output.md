# Existing-handle source outputs

Current update: [publication separation](helios-source-publication-separation.md)
now closes election-level existing-handle output by all-target exclusion for
reached fresh elections. Earlier statements leaving that case open below are
historical; raw matching and bound-output frame presentation remain open.

Status: **machine-checked** generic output closure and canonical derivation.
B9/B10 remain open at 8/10 unweighted milestones (80%).

An output labelled by an existing variable keeps the old frame domain. This
increment closes the generic target-class obligation for that source rule.
It does not yet classify these actions against the election's publication
phases, whose current wrapper always introduces a fresh handle.

## Checked interface

- `Extended.FreeStep.output_sameRealizations_target` takes an actual raw
  free output and a complete source realization class for `frameProcess φ p`.
  If every visible continuation emitting a value E-equal to the labelled
  `φ.value x` agrees with `q`, the entire raw target class is
  `frameProcess φ q`. Both directions quantify over all environments/bodies.
  Every old handle is constrained, including handles not used by the label.
- `Extended.FreeStep.output_of_sameRealizations` returns a real visible
  output, its full value equal to the labelled old handle, and a target
  realization. No normalization or output reconstruction premise is assumed.
- `Named.JointOpening.handle_output_step` retains the literal public channel
  and full old-handle equality across fresh name openings.
  `handle_output_target` retains the old policy, old domain and complete joint
  target. `handle_output` combines these with global output determinism.
- `Extended.frame_handle_output_derivable` and
  `Named.restricted_handle_output_derivable` construct actual old-handle
  outputs from canonical prefixes that emit exactly that handle's full value.
  The latter requires a public channel. Active substitutions, Out-Atom and
  name Scope supply the derivation; no new operational rule is introduced.

The target proof uses forward and backward realization transport. The named
proof opens both canonical endpoints in shared fresh coordinates, fixes the
public channel, moves complete frame values through inverse permutations and
rebuilds a nonempty joint target. It does not infer Structural equivalence from
semantic equality. The derivation theorem is a separate canonical construction.

## Controls and source correspondence

`SourceHandleOutputSPOT` has twelve public kernel controls. Its two-entry frame
contains SPK values identical except for fourth-field names 99 and 98. Output
on channel 8 uses handle 0 and leaves an input continuation on channel 9.
The other label, handle 1, is rejected for every raw target. Changing either
the emitted or the unemitted frame entry also invalidates target realization.
A projection E-equal to the first payload is accepted, checking that the proof
preserves equality modulo full E rather than requiring literal environment
identity. Parallel null components exercise noncanonical raw endpoints.
A private channel remains blocked after the output.

The reality oracle is Cortier–Smyth Figure 3 Out-Atom, Subst and Scope: this
label exports no fresh variable. Full E/E0, the SPK fourth field, structured-key
E5, full-ciphertext E6 and explicit public observations remain unchanged.
These are directed kernel controls and general proofs; no new randomized
cryptographic campaign or security claim from search failure is made.

Integrated verification: `lake build` passes **4064 jobs**. The current log
reports **4453** nonempty standard-only and **91** axiom-free results. The claim
audit covers **3558** public theorem entries and **124** current-status documents.
All six changed Lean sources have current oleans; **1601** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **19** theorem audits,
including **12** public kernel controls, and no production definitions.
The targeted control build passes **1420 jobs**.
Build log: `tmp/variable-overlap/source-handle-output-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-handle-output-verification.txt`.

## Remaining boundary

The generic existing-handle closure is complete. Its election-level treatment
is still required: prove when old-handle outputs are impossible, or extend the
phase relation with the corresponding old-domain behavior. Do not silently
count such an output as a fresh-handle publication.

Construction of matching actions in arbitrary related raw counterparts, raw
bound-output frame Structural presentation, the final paired relation and all
weak labelled bisimulation/secrecy clauses remain open. The reconstruction
audit confirms only that current `WellFormed` supplies scope and unique
definitions; it supplies no normalization theorem. No checked cyclic
counterexample or implication from `JointOpening` to `Structural` is claimed.

See the [blueprint](helios-proof-blueprint.md),
[coordinated phases](helios-source-coordinated-phases.md),
[task list](../../task%20list.md) and [results ledger](helios-results.md).
