# Captures with interleaved private-name scopes

Current follow-up: [structural action openings](helios-source-structural-openings.md)
retain actual binder-structural endpoint paths and characterize Named structure
by jointly fresh structural openings. General reachable reconstruction and
final secrecy remain open.

Status: **machine-checked** raw output and reconstruction for the existing
ScopedTermProgram class. Reconstruction retains its stated freshness premises;
general reachable normalization and secrecy remain unproved. B9/B10 stay at
8/10 unweighted milestones.

## Actual scoped output

`SourceScopedProgramCapture` reuses ScopedTermProgram, whose local computations
can contain interleaved base-name binders. The new capture description keeps
every original local/name scope and performs the required variable exchange.
`compile_output_capture` derives that exact raw target through original Named
rules. It does not require Hoistable, normalize the source first or introduce
an operational rule. Base-name binders do not hide the static channel.

`capture_hoist` uses the existing Hoistable predicate: later name binders must
not capture literals in earlier local providers. It hoists the actual output
target, including the variable exchanges, to an explicit name prefix around the
erased TermProgram capture. `capture_normalizes` then eliminates its dependent
locals by the earlier computed-capture theorem. Full capture values remain.

## Complete frame and private policy

`SourceScopedCaptureFrames.frame_scoped_program_capture_normalize` additionally
requires every program binder to avoid the complete old frame's nameSupport.
This permits extrusion over the old active providers, whose values are retained
exactly. Program Hoistable alone does not supply this separate frame condition.
The resulting public value is precisely the erased program value evaluated in
the old frame, with the complete extended public domain under outputHandle.

`scoped_program_prefix_policy` identifies the actual combined prefix with the
old restricted set union program.names.toFinset, while keeping the original
hidden channels. Existing structural prefix reordering and deduplication justify
this equality of source restrictions, even with repeated program names. This is
an actual restriction proof, not an unused-name policy-padding argument.

`restricted_scoped_program_capture_normalize` gives the complete canonical
Named target with that private policy; its represents theorem gives an actual
ground frame presentation. `restricted_scoped_program_output` supplies both the
original action and its fully reconstructed target on a channel outside hidden.
Freshness is stated over full old values, not merely visible tallies or recipe
syntax. These theorems do not claim privacy of what the output releases.

## Controls and evidence

Twenty-two SourceScopedCaptureSPOT controls retain two dependent locals with
private name 50 between them and private name 51 inside both. An independently
written raw target pins these positions and the exported handle outside the
locals. Original output, actual hoisting, full SPK capture, all three final
values, full Named presentation and static observation are checked.

The exact private policy is {40,50,51}. Omitting the program names would wrongly
allow the literal nonce 50 as an attacker recipe; the captured public handle
remains a valid recipe. Changing a literal from 51 to 52 is E-distinct in the
fixed coordinates; this is not a claim forbidding fresh alpha conversion.
A later name cannot capture an earlier literal provider, and program hoistability
alone does not protect a colliding old frame value. Both failed-premise fixtures
still have actual original outputs. A repeated name [50,50] has an actual complete
presentation with one policy entry. A private base 50 still permits channel 50.

Formal oracle: induction on existing syntax and original Named structural/output
rules, with directed kernel fixtures. Reality oracle: Figure 3 capture-avoiding
extrusion, sorted restrictions and Scope. Full E/E0, every SPK field, structured-key
E5, full-ciphertext E6 and explicit observations remain unchanged. No new
randomized cryptographic campaign or source operational rule is claimed.

Integrated verification: `lake build` passes **4090 jobs**; targeted controls
pass **1166 jobs**. The current log reports **4678** nonempty standard-only and
**92** axiom-free results. The claim audit covers **3784** public theorem entries
and **131** current-status documents. All five changed Lean sources have current
oleans; **1675** local links resolve. No proof holes, custom axioms, warnings or
errors were found in the checked scope; `git diff --check` passes. This increment
adds **30** theorem audits, including **22** public kernel controls, and one raw
target definition (ScopedTermProgram.capture), with no new program datatype or
operational rule.
Log: `tmp/variable-overlap/source-scoped-capture-full-build.log`.

## Remaining obligation

Extract solvable presentations from arbitrary reachable structural representatives,
including representatives outside the current syntax/freshness conditions. The
[Named execution invariant](helios-source-rigid-execution.md) is necessary but has
not been proved sufficient for that extraction. General raw action matching,
general output frame presentation and final paired weak labelled bisimulation
and secrecy remain open. The [old-handle election case](helios-source-publication-separation.md)
remains closed.

See the [blueprint](helios-proof-blueprint.md), [task list](../../task%20list.md)
and [results ledger](helios-results.md).
