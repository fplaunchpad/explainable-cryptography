# Joint visible transitions and common fresh input policy

Current update: [existing-handle output closure](helios-source-handle-output.md)
now proves the generic free-output class/joint target obligation. Election-level
old-domain treatment remains open. Earlier open-closure statements below record
the historical boundary; arbitrary raw matching and final secrecy remain open.

Current frontier: [coordinated phases](helios-source-coordinated-phases.md) now
classify arbitrary inputs after common freshening and retain shared coordinates
through later internal traces and bound outputs. Arbitrary raw partner action
construction and final secrecy remain open. Earlier limits below describe
their historical checkpoint.

Status: **machine-checked** joint public-input and bound-output closure, actual
election output-phase closure, and common fresh input policy with full target
preservation. B9/B10 remain incomplete at 8/10 unweighted milestones (80%).
Final weak labelled bisimilarity and symbolic secrecy remain unproved.

## Endpoint and observation names

[SourcePairedOpeningObservations](../../ExplainableCrypto/Helios/Symbolic/SourcePairedOpeningObservations.lean)
constructs paired openings across different variable domains, retaining finite
faithfulness and the assignment outside the original restriction prefix.
`prefix_permutations_fixed_pair` uses a supplied finite set containing both
endpoint supports and the relevant observation names. The resulting common
base/channel permutations describe both endpoints and fix every supplied name
outside the prefix. `input_label_fixed` retains the complete input recipe,
including the fourth SPK field, and its literal channel.

## Public inputs and complete bound outputs

[SourceJointPublicInput](../../ExplainableCrypto/Helios/Symbolic/SourceJointPublicInput.lean)
proves `JointOpening.public_input_step`: an actual raw input whose recipe is
Public under the canonical policy has an actual canonical input with the exact
same channel and evaluated recipe. Public channel membership is derived from
the source action and joint relation. `public_input_target` retains JointOpening
with the same restrictions/frame and a deterministic canonical continuation.
`public_input` constructs that continuation under full input determinism.

[SourceJointBoundOutput](../../ExplainableCrypto/Helios/Symbolic/SourceJointBoundOutput.lean)
proves `output_step`, `output_target` and `bound_output`. The raw output has an
actual canonical output on the same literal channel. After outputHandle
renaming, the complete raw target is jointly related to the restricted state
with frame φ.extend m and full continuation q. Every old handle and the entire
new message survive. The paired target opening has a different variable domain;
its allocation and actual restrictions are retained. The generic premise is
determinism of both full output values modulo E and complete continuations.

All closure proofs refresh against the union of target free names, both
canonical endpoint supports and the observation support. They preserve a
nonempty complete realization class and add no source operational rule.

## Arbitrary input labels

The fixed-original-policy alpha-input counterexample remains valid: after
renaming private name 40 to 41, an actual source input can use literal 40, even
though that recipe is not Public under the old policy {40}.

[SourceJointFreshInput](../../ExplainableCrypto/Helios/Symbolic/SourceJointFreshInput.lean)
proves `JointOpening.common_fresh_input`. Given the two actual canonical
partners with statically equivalent full frames, it constructs one fresh
base/channel permutation for both. Actual Structural derivations justify both
changes. The raw processes and input label remain unchanged. The recipe is
Public under the fresh policy, the public channel is fixed, and both source
joint relations and full old-frame StaticEq are retained. An actual ScopedStep
with that same input label leads to the raw target's complete joint relation.
Publicness is derived through common freshening; it is not assumed for the old
private-name policy or an arbitrary inverse-permuted recipe.

## Election transitions

[SourceElectionJointVisible](../../ExplainableCrypto/Helios/Symbolic/SourceElectionJointVisible.lean)
discharges generic input/output determinism with the all-residual election
theorems. `source_joint_common_fresh_input` uses reachable-frame StaticEq in
either vote-world direction and constructs both fresh source relations and the
actual input target. It does not yet return a check-phase relation with the
fresh coordinates tracked across subsequent actions.

`source_joint_output_next` is stronger: it identifies the full Publication,
its actual stage Step, the literal broadcast channel and PhaseJointOpening at
the next phase. `Publication.next_handles` and `.target_state` give the exact
new domain and full canonical frame/body transport. This covers every actual
raw bound output from an in-range phase under channel freshness; no canonical
Structural presentation of the raw source or target is assumed.

## Controls and verification

[SourceJointVisibleSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceJointVisibleSPOT.lean)
has 22 public kernel controls. They cover exact public-handle input, private
continuation blocking, full scoped SPK capture, wrong fourth fields and old
values, competing outputs, the actual alpha input under a common derived fresh
policy, full observation support and actual first-publication phase closure in
both vote worlds. The alpha fixture explicitly retains the original negative
Public {40} result as well as the positive fresh-policy action and target.

The gate uses directed semantic kernel fixtures and general proofs. No new
randomized cryptographic campaign or inference from failed search is claimed.
Historical In/Out/Open/Scope and alpha rules supply the model reference, with
independently specified messages, recipes and phase fixtures. Full E/E0, all
cryptographic fields and explicit public observations are unchanged.

Integrated verification: `lake build` passes **4053 jobs**. The log reports
**4397** nonempty standard-only and **91** axiom-free results. The claim audit
covers **3502** public theorem entries and **122** current-status documents.
All eight changed Lean sources have current oleans; **1565** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **37** theorem audits,
including **22** public kernel controls, and no production definitions.
The targeted control build passes **1424 jobs**.
Build log: `tmp/variable-overlap/source-joint-visible-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-joint-visible-verification.txt`.

Next: retain common canonical coordinates in the phase relation and complete
input-stage matching across freshening, then source-action construction in
arbitrary related representatives, existing-handle free-output closure,
output-frame Structural presentation and final bisimulation/secrecy. Neither
joint target closure nor old-frame StaticEq alone proves the final matching
direction or static equivalence of arbitrary raw output frames. See the
[blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md) and
[task list.md](../../task%20list.md).
