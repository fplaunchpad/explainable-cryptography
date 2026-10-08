# Reconstructing captures through dependent local computations

Current follow-up: [scoped program captures](helios-source-scoped-capture.md)
now handles interleaved ScopedTermProgram base-name/local scopes under Hoistable
and old-frame name freshness, with actual full combined-policy presentations.
General reachable reconstruction and final secrecy remain open.

Status: **machine-checked** original Scope output and target reconstruction for
every finite existing TermProgram. General reachable normalization and final
secrecy remain unproved; B9/B10 stay at 8/10 unweighted milestones.

## Local Scope and continuation coordinates

`SourceLocalCaptureNormalization.swap_then_bind_local` identifies the exact
composition of Scope's swapBinders and subsequent local elimination. Fresh None
remains the exported variable. The eliminated local is substituted through the
older Some positions, including beneath future input binders.

`scope_capture_normalize` derives an original Structural path for a complete
local provider, fresh capture and arbitrary plain continuation after Scope.
The provider may depend on old variables; the capture may depend on that local.
The proof instantiates the local only after the binder exchange, then uses the
existing let_normalize/Subst/Alias derivation. The public payload is precisely
shiftTerm of bindInput applied to the capture recipe and local definition.
The continuation uses liftSubst of that same input substitution. Neither its
free variables nor its input binders are erased.

## Actual dependent program output

`SourceTermProgramCapture` reuses the existing TermProgram datatype. The new
`TermProgram.capture` describes the actual raw output target: the result case
captures its full term, and every let retains its provider and local restriction
with the original Scope exchange. It adds no program datatype or action rule.

`compile_output_capture` constructs the original BoundOutput through every
Scope and parallel provider. It does not first normalize the source or choose a
more convenient target. `capture_normalizes` eliminates those actual retained
locals, by induction and the single-scope lemma, to the complete computed capture.
`capture_exports_iff` identifies the sole public export of this computation;
the old public domain is supplied separately by the retained provider frame.

`frame_program_capture_normalize` combines the computed capture with all old
providers and outputHandle to derive the complete extended frame.
`frame_program_output` supplies both the actual action and full reconstruction.
Named restricted_program_capture_normalize/represents retain the same sorted
name prefix and give an actual frame presentation. restricted_program_output
constructs the original Named action and complete target on any channel outside
the hidden-channel set. These output theorems do not claim secrecy of the value.

## Controls and evidence

Twenty-one public controls in SourceProgramCaptureSPOT use two dependent locals:
x is old handle 0, and y is pair(x,old handle 1). An independently written raw
target retains both restrictions, with the fresh capture outside both. The
computed full SPK payload is grounded using old values 40 and 41, and all three
final handles remain explicit. Actual Extended and Named outputs, full frame
presentations and static observations are retained.

Changing the first payload field from 40 to 41 is E-distinct and cannot be the
same structural target. Merging the fresh capture into an old handle contradicts
its actual exported domain. A separate arbitrary continuation keeps its input,
exported value and local 40 distinct; replacing that local by 41 is rejected.
Both the normalized and unnormalized scoped continuation perform the same
actual input, retaining the full target, so the example is not stuck.

Formal oracle: finite existing-program induction, exact instantiation and
original Structural/BoundOutput rules, with directed kernel fixtures. Reality
oracle: Figure 3 Scope exchanges the local and exported variables; Alias removes
only an independent local provider after substitution. Full E/E0, SPK's fourth
field, structured-key E5, full-ciphertext E6 and explicit observations remain
unchanged. No new randomized cryptographic campaign is claimed.

Integrated verification: `lake build` passes **4087 jobs**; targeted controls
pass **1152 jobs**. The current log reports **4648** nonempty standard-only and
**92** axiom-free results. The claim audit covers **3754** public theorem entries
and **130** current-status documents. All five changed Lean sources have current
oleans; **1683** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **31** theorem audits, including **21** public kernel controls, and one raw
target definition (TermProgram.capture), with no new program datatype or
operational rule.
Log: `tmp/variable-overlap/source-program-capture-full-build.log`.

## Remaining obligation

Extract solvable local computations from arbitrary reachable structural
representatives. This theorem covers finite TermProgram computations and a
general single local capture context; it does not characterize every raw target
in the full source calculus. The scoped extension now handles interleaved
ScopedTermProgram names under Hoistable and full old-frame freshness. General raw action
matching, general output frame presentation and final paired weak labelled
bisimulation/secrecy remain open. The [Named execution invariant](helios-source-rigid-execution.md)
and [old-handle election exclusion](helios-source-publication-separation.md) remain checked.

See the [blueprint](helios-proof-blueprint.md), [task list](../../task%20list.md)
and [results ledger](helios-results.md).
