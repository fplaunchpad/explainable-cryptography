# Explicit source board tally computations

Status: machine-checked. At the tallying stage, the Figure 4 block with one
local tally definition per candidate normalizes through actual source structural
rules to `boardFinish`. This holds for every positive candidate count, arbitrary
full ballot terms and any finite list of additional ballots. The continuation
sends the complete tuple privately, receives the trustee partial tuple, then
publishes the partials and ordered results. Its decryptions use the saved
candidate registers directly.

This closes tally-block computation at the reached stage. The current plain
`Agent` syntax does not encode extended let continuations beneath the preceding
ballot inputs and guards. Connecting that complete syntactic expansion remains
part of B9. The result is not a full source secrecy theorem.

## Source rules and finite substitution

[SourceAgentProgram.lean](../../ExplainableCrypto/Helios/Symbolic/SourceAgentProgram.lean)
adds a construction language with `result` and `letTerm`. Its compiler uses
only existing restricted active providers. `AgentProgram.eval_value` connects
environment evaluation with exact continuation substitution;
`compile_normalizes` gives an actual `Extended.Structural` path to that
continuation, including all later inputs and branches. `compile_no_exports`
excludes leaked local domains.

[SourceFiniteSubstitution.lean](../../ExplainableCrypto/Helios/Symbolic/SourceFiniteSubstitution.lean)
proves `Agent.bind_structural` from Alias, Subst and active E rewriting.
`subst_update_structural` changes one supplied value in an arbitrary process.
`finite_subst_structural` iterates that construction over a finite variable
environment whose values are pointwise full-E equal. It retains all future
binders, guards and output prefixes. It does not assert an unrestricted lift
from `Agent.EquivE` to source structure.

## Exact candidate bindings

[SourceBoardTallyProgram.lean](../../ExplainableCrypto/Helios/Symbolic/SourceBoardTallyProgram.lean)
keeps the original per-candidate expressions separate from saved registers,
which initially contain bottom. Each let computes its candidate's product and
updates that register to the new bound variable, shifting all earlier variables.
`BoardTallyRegisters.afterBind_map` and `completed_compute` establish the exact
register update. `boardTallyComponents_eval` covers every supplied index list,
so skipped candidates remain observable. `boardTallyProgram_value` proves the
exact direct-register continuation for the full candidate list;
`boardTallyProgram_bindings` proves exactly `n+1` lets.

The products use the existing nonempty `boardTally` fold: the two honest
ciphertext projections seed it, and every additional ballot contributes its
projection. No new multiplication identity or cryptographic equation is added.

## Actual source correspondence

[SourceBoardTallyBridge.lean](../../ExplainableCrypto/Helios/Symbolic/SourceBoardTallyBridge.lean)
uses a finite template to relate direct tally references to tuple projections.
The template's first variable supplies the unchanged private message, and the
remaining variables supply the candidate values for the final decryptions.
`boardRegisterFinish_structural` rewrites those supplied values using full E;
`boardTallyProgram_normalizes` composes that path with let elimination.

`computedBoardTallyState_normalizes` retains the whole public frame, trustee
and allocated base/channel restrictions and reaches the existing `sendTally`
source state. Its reduction/free/bound iff lemmas preserve arbitrary actual
targets and exact labels. Presentation and well-formedness are unconditional;
`computedBoardTallyState_staticEq` requires fresh names and a reachable tallying
stage and supplies its full static witness. `computedBoardTallyState_sends`
derives the actual private tally communication to `trusteeReply`.

## Controls and verification

[SourceBoardTallySPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceBoardTallySPOT.lean)
retains nineteen public kernel controls. Independently written fixtures cover
two candidate products from three ballot payloads, the entire ordered
continuation, one-candidate/two-ballot computation, and distinct saved variables
beneath a fresh trustee input. Omitted-candidate and copied-candidate mutants
fail; a captured tally is different from the intended continuation. The
no-export control quantifies over an inhabited outer variable type. Actual
Named well-formedness, static witnesses and private communication are checked.

The separating algebra is used only to refute full-E equality of the wrong
products. It is not attacker evaluation. Structural/substitution claims have
general kernel proofs and directed controls; there is no new randomized
cryptographic campaign or search-based security claim.

Integrated verification at this board-tally checkpoint: `lake build` passes **3942 jobs**. The log reports
**3598** nonempty standard-only and **64** axiom-free results. The claim audit
covers **2676** public theorem entries and **106** current-status documents.
All seven changed Lean sources have current oleans; **1309** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **44** theorem audits,
including **19** public kernel controls, and checks eleven construction and
compilation definitions. Build log:
`tmp/variable-overlap/source-board-tallies-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-board-tallies-verification.txt`.

Reality oracle: Figure 4 in the local Cortier–Smyth paper, especially the board
block in `tmp/cortier-smyth-layout.txt`. The candidate tally lets precede the
private send, and the final decryptions refer to the individual saved tallies.

Remaining obligations: general Named source correspondence, canonical environment/body correspondence, remaining
admissibility and final weak labelled bisimilarity/symbolic secrecy. Full E and
the existing source structural and action rules are unchanged. B9/B10 remain
open at eight of ten unweighted milestones; maintain the
[blueprint](helios-proof-blueprint.md), [results](helios-results.md) and existing
item in [task list.md](../../task%20list.md).

The subsequent [voter-scope increment](helios-source-voter-scopes.md) establishes
interleaved nonce placement in the actual initial election and fresh allocation
for arbitrary full ground candidate parameters.

The later [guarded board increment](helios-source-guarded-board.md) retains this
block beneath the full input/guard chain in construction syntax. It proves
exact substitution, actual source activation and compiled process congruence.
Its compilation convention adds no structural rule beneath source prefixes.

[Independent frame compatibility](helios-source-frame-compatibility.md) now
proves common-policy presentation compatibility and Named.StaticEq transitivity.
Fresh/injective assignment selection and general action matching remain open.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.
