# Visible realization classes and the restriction-policy boundary

Current follow-up: [structural action openings](helios-source-structural-openings.md)
retain actual binder-structural endpoint paths and characterize Named structure
by jointly fresh structural openings. General reachable reconstruction and
final secrecy remain open.

Current update: [existing-handle output closure](helios-source-handle-output.md)
now proves the generic free-output class/joint target obligation. Election-level
old-domain treatment remains open. Earlier open-closure statements below record
the historical boundary; arbitrary raw matching and final secrecy remain open.

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

Current frontier: [joint fresh openings](helios-source-joint-openings.md) now
retain actual channel restriction and reject the counterexample below.
Their operational closure and final secrecy remain open. The prior invariant
and its stated limits remain as recorded here.

Status: **machine-checked** input and bound-output preservation of the complete
canonical-opening invariant. The fresh output handle and all old frame values
are retained. Every election residual has the required visible determinism on
all channels. **Refuted:** the current body invariant alone preserves channel
restriction. B9/B10 remain incomplete at 8/10 unweighted milestones (80%);
final weak labelled bisimilarity and symbolic secrecy remain unproved.

## Backward visible realization

[SourceBackwardVisibleRealization](../../ExplainableCrypto/Helios/Symbolic/SourceBackwardVisibleRealization.lean)
proves `Extended.FreeStep.realizes_backward` for every free-action constructor,
variable Scope, parallel context and structural pre/post path. Every full target
realization yields a full source realization in the same environment, the same
RealizedStep label and an actual visible target EvalEq to the chosen target
body. Input retains the exact evaluated recipe. Existing-handle output retains
its environment value modulo full E. `has_realization_iff` preserves exactly
which environments admit a realization.

`BoundOutput.realizes_backward` starts with a full target realization in
`extendEnv env m`. It constructs a source realization in `env`, an actual
output of a complete value `n`, `EqE m n`, and an EvalEq target body. The proof
retains the old environment and correctly exchanges the fresh output/local
variable slots beneath Scope. These theorems do not add EvalEq closure to the
original source action relations; they use the existing interpretation quotient.

## Complete input and fresh-output target classes

[SourceInputRealizationClosure](../../ExplainableCrypto/Helios/Symbolic/SourceInputRealizationClosure.lean)
proves `FreeStep.input_sameRealizations_target`. The source has exactly the
full realizations of `frameProcess φ p`, for all environments and bodies.
Determinism is required for the canonical input of the complete recipe value
`φ.eval r`. Every target realization is then exactly a realization of
`frameProcess φ q`. Pointwise E-equivalent old environments evaluate the input
recipe modulo E; input transport preserves its full continuation.

[SourceOutputRealizationClosure](../../ExplainableCrypto/Helios/Symbolic/SourceOutputRealizationClosure.lean)
proves `BoundOutput.capture_realizes_iff`. Under explicit deterministic full
output value and continuation, a target realization is equivalent to all old
frame constraints, equality of the captured value with the entire emitted
message modulo E, and the complete target body modulo EvalEq.
`outputHandle_environment_split` covers every fresh-handle environment.
`BoundOutput.sameRealizations_target` concludes that the renamed raw target has
exactly all realizations of `frameProcess (φ.extend m) q`. This is a complete
semantic frame class; it is not a proof of Named.RepresentsFrame's required
Structural presentation.

## Paired visible openings and coherent coordinates

[SourcePairedVisibleOpenings](../../ExplainableCrypto/Helios/Symbolic/SourcePairedVisibleOpenings.lean)
opens both endpoints with one assignment and allocation, even when bound output
changes the variable type. The assignment is fixed outside the original name
prefix. Existing label freshness proves that the complete free label, or the
bound-output channel, is unchanged under literal outer assignment.
`FreeStep.opening_step` and `BoundOutput.opening_step` start with actual Named
actions and construct actual paired Extended actions, both full-realization
comparisons and openings of the unchanged raw targets. Any extra finite
avoidance set is retained. No assumed reconstruction witness is required.

[SourceVisibleDeterminismPermutations](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleDeterminismPermutations.lean)
transports input determinism at fixed channel/full message and output
determinism of both complete values and continuations through coherent
permutations.
[SourceCanonicalOpeningVisible](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalOpeningVisible.lean)
proves `HasCanonicalOpening.input` and `.boundOutput`. Inputs retain the old
frame; bound outputs rename the actual fresh variable to outputHandle and extend
the full frame. Both retain the complete opening invariant on their raw targets.
The canonical label is explicit: channel `k.symm c`, and for input the recipe
`r.mapNames e.symm`. Publicness or same-label alignment of these transformed
observations is not a conclusion of the theorem.

[SourceElectionVisibleDeterminism](../../ExplainableCrypto/Helios/Symbolic/SourceElectionVisibleDeterminism.lean)
proves complete active input/output uniqueness for every channel of every
residual. Fresh channels separate simultaneous private/public prefixes. The
proof covers both zero and positive remaining input counts; no reachability or
in-range premise is needed. Input determinism retains the entire target, while
output determinism retains the full emitted value as well as its continuation.
[SourceElectionVisibleInvariant](../../ExplainableCrypto/Helios/Symbolic/SourceElectionVisibleInvariant.lean)
discharges the generic closure premises with these election theorems. The
canonical visible action is retained with explicitly transformed coordinates;
public-label policy and next-phase identification remain separate.

## Checked policy counterexample

The controls construct an unrestricted `embed (frameProcess φ outputCode)` and
the same canonical frame/body beneath a restriction of output channel 8.
Both satisfy `HasCanonicalOpening` for the same φ and outputCode. The
unrestricted process has an actual BoundOutput on 8. The restricted canonical
state has no BoundOutput on 8, through any structural derivation or to any raw
target, by the checked source channel-scope theorem.

Thus the body invariant alone does not preserve restriction policy and cannot
serve as the final bisimulation relation. This is a checked falsifier, not a
failed proof search. It does not refute the stated source-action-consumption
or target-class preservation results. They explicitly transform canonical
coordinates and do not assert policy alignment. The final relation must also
retain sufficient nominal restriction information. [Joint fresh openings](helios-source-joint-openings.md) now compare the raw
process with the actual restricted canonical process and derive simultaneous
finite avoidance and actual free-channel preservation. They exclude this
counterexample and require a nonempty realization class. Operational closure
and public input-recipe/phase alignment remain open; do not add them as assumed
callbacks.

## Controls, verification and remaining work

[SourceVisibleInvariantSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceVisibleInvariantSPOT.lean)
has 29 public kernel controls. They cover actual complete SPK output, backward
capture, all target environments after fresh-handle renaming, wrong fourth
fields and wrong old handles, waiting continuations, variable-Scope exchange,
exact handle-recipe input, all old input environments, competing inequivalent
outputs, actual Named input/output invariant closure and all-residual visible
determinism. The explicit restriction-policy counterexample is retained.

The gate is general induction and independently specified positive/negative
kernel controls. No randomized cryptographic campaign or security inference
from search failure is claimed. Figures 2–3 In/Out/Open/Scope and active
substitution semantics supply the reality reference. Full E/E0, complete fields
and explicit public observations are unchanged. No production definition,
source action or custom axiom is added by this increment.

Integrated verification: `lake build` passes **4039 jobs**. The log reports
**4294** nonempty standard-only and **90** axiom-free results. The claim audit
covers **3398** public theorem entries and **119** current-status documents.
All eleven changed Lean sources have current oleans; **1534** local links
resolve. No proof holes, custom axioms, warnings or errors were found in the
checked scope; `git diff --check` passes. This increment adds **51** theorem
audits, including **29** public kernel controls, and no production definitions.
The targeted control build passes **1411 jobs**.
Build log: `tmp/variable-overlap/source-visible-invariant-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-visible-invariant-verification.txt`.

Remaining: restriction/public-policy information in the relation, coherent
same-label and next-phase alignment, action construction in arbitrary related
raw processes, existing-handle free-output target-class closure, output frame
Structural presentation and the final weak labelled bisimulation/secrecy theorem.
Earlier internal trace preservation and both-world one-step matching from
canonical Structural representatives remain proved. See the
[blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md) and
[task list.md](../../task%20list.md).
