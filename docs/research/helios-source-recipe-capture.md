# Full provider substitution and recipe capture reconstruction

Current follow-up: [scoped program captures](helios-source-scoped-capture.md)
now handles interleaved ScopedTermProgram base-name/local scopes under Hoistable
and old-frame name freshness, with actual full combined-policy presentations.
General reachable reconstruction and final secrecy remain open.

Current follow-up: [dependent program captures](helios-source-program-capture.md)
now reconstructs actual Scope targets for every finite existing TermProgram,
including dependent local definitions and full Named frame presentations.
General extraction through reachable structural representatives remains open.

Status: **machine-checked** reconstruction for an explicit ground provider frame
beside a fresh recipe-valued capture. General reachable normalization remains
open. B9/B10 stay at 8/10 unweighted milestones; secrecy remains unproved.

## Full context substitution

`SourceFrameContextSubstitution` extends the existing plain-continuation frame
substitution theorem to arbitrary Extended contexts, including active payloads
and local binders. Each original Subst step retains its provider, and parallel
rearrangement retains the rest of the exact frame.

`frameEntries_apply_extended` returns an exact Instantiates graph for entriesSubst
and an original Structural path for the complete frame/context pair. Its premise
requires that the context not export any provider variable. It does not require
injectivity of an arbitrary provider list: sequential application remains defined
for repeated providers, with the same possibly ill-formed frame retained.
`frameEntries_apply_instantiates` identifies any supplied exact target by the
existing uniqueness theorem. No new substitution operation is defined.

`entriesSubst_outside` leaves every variable outside the provider domain fixed.
For the shifted canonical frame, `entriesSubst_shifted_frame` grounds each old
Some with its own full value and leaves fresh None as a variable. This uses
injectivity of Some. `shiftedFrame_apply_instantiates` applies those old bindings
to any context that does not redefine them, including one exporting fresh None.

## Actual capture reconstruction

`frame_recipe_capture_ground` starts with the shifted complete old active frame,
a fresh binding None to shiftTerm r, and any plain continuation over old and new
handles. The recipe r is arbitrary. Old-frame substitution evaluates the capture;
Subst from the new provider then evaluates every continuation use. New input
binders stay local. The resulting continuation is exactly p.subst applied to
extendEnv of the old values and the full recipe value.

`frame_recipe_capture_normalize` applies outputHandle and derives an original
Structural path to the full extended frame and that evaluated continuation.
`frame_recipe_output` also supplies the actual original bound output for a raw
non-ground output prefix. The result includes both the derivation and its
complete canonical target; no emitted-value or normalization callback is assumed.

`Named.restricted_recipe_capture_normalize` retains the same actual sorted name
prefix throughout the complete reconstruction. `restricted_recipe_capture_represents`
gives a genuine ground-frame presentation for this class. `restricted_recipe_output`
constructs an original Named output and its full target when the channel is
public under the existing hidden-channel set. The recipe itself need not be a
public attacker recipe: a protocol output can release its value, and this theorem
does not assert privacy of that release.

## Controls and evidence

Eighteen public SourceRecipeCaptureSPOT controls use two distinct old values,
40 and 41, a full SPK payload with old-handle references in its fourth field,
and an input continuation using both the capture and an old handle. They retain
all three final handle values, exact Option/Fin naming, an actual Named frame
presentation and static witness. Changing the final literal in the fourth field
from 42 to 43 is E-distinct and cannot yield the same structural target.

A separate local-variable and input-binder fixture grounds the local definition
while preserving the input, local and fresh-capture coordinates. The provider
frame remains exact. The new None is never grounded by old providers. Redefining
an old provider in the context violates the side condition, and removing its
constraint cannot justify grounding a dependent active value. Real Extended and
Named non-ground outputs retain their whole reconstructed targets.

Formal oracle: finite provider induction and exact instantiation/structural
conclusions in Lean. Reality oracle: Figure 3 retained-provider Subst, original
parallel/Scope rules and fresh variable output. Full E/E0, all SPK fields,
structured-key E5, full-ciphertext E6 and explicit public observations remain
unchanged. No new randomized cryptographic campaign or operational rule is claimed.

Integrated verification: `lake build` passes **4084 jobs**; targeted controls
pass **1148 jobs**. The current log reports **4618** nonempty standard-only and
**91** axiom-free results. The claim audit covers **3723** public theorem entries
and **129** current-status documents. All five changed Lean sources have current
oleans; **1661** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **30** theorem audits, including **18** public kernel controls, with no new
production definition or operational rule.
Log: `tmp/variable-overlap/source-recipe-capture-full-build.log`.

## Remaining proof obligation

Extract this explicit provider/capture form through arbitrary reachable
structural representatives, retaining enough information to eliminate their
local definitions. The [Named execution invariant](helios-source-rigid-execution.md)
is necessary but has not been proved sufficient for that extraction. General raw
bound-output frame presentation, matching from arbitrary raw partners and the
final paired weak labelled bisimulation/secrecy theorem remain open. The
[old-handle election case](helios-source-publication-separation.md) remains closed.

See the [blueprint](helios-proof-blueprint.md), [task list](../../task%20list.md)
and [results ledger](helios-results.md).
