# Renamed public frames and scoped actions

B9 now preserves and reflects full public-frame static equivalence and every
evaluated scoped step under independent base-name/channel permutations. The
active-frame representation and raw output capture commute with the same map.
These are machine-checked supporting results. The subsequent
[explicit name-restriction bridge](helios-source-name-restrictions.md) now adds
sorted name binders, New/Scope/alpha rules and forward derivations through those
binders. Arbitrary structural/alpha closure, named-frame observations and the
full source converse remain to be connected, along with outer voter construction;
B9/B10 stay at 8/10 unweighted milestones (80%).

## Public observations

[SourceNameFrames.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameFrames.lean)
defines `Frame.mapNames`: every handle keeps its index and complete payload,
and the restricted-name policy becomes its image under the base-name map.
Evaluation commutes with consistent recipe/frame renaming. Frame extension
commutes with renaming the emitted value; old handles remain old and the new
value still occupies the last handle. Permutations make frame mapping injective.

`Frame.staticEq_mapNames_iff` quantifies over all public recipes under the
corresponding policies. Its forward direction pulls arbitrary renamed recipes
back through the inverse permutation, applies original static equivalence and
transports full E equality. Its reverse direction maps each original public
recipe forward. This preserves the full observation relation, with no tally-only
or restricted recipe-language replacement.

## Evaluated scoped transitions

[SourceNameScoped.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameScoped.lean)
maps `ScopedState` and `PublicEvent`. Input labels retain recipes with their
literal names renamed. Output labels still contain only their renamed channel
and bind the next handle; they do not acquire a public ground payload field.
Hidden channels use the channel permutation, independently of the base-name
restriction policy.

`ScopedStep.mapNames` derives each renamed tau/input/output step.
`scopedStep_mapNames_iff` reflects every renamed step. Input reflection recovers
recipe publicness and exact evaluated behavior. Output reflection recovers the
entire emitted value through the inverse base-name permutation and uses frame
injectivity to recover the exact extended frame. Internal actions keep their
frame and remain possible on private channels.

These theorems concern the existing evaluated wrapper. Mapping its fixed hidden
channel set does not implement syntactic name restriction, source Scope or
bound-name alpha-conversion. The operational converse for arbitrary extended
source derivations remains a separate open obligation.

## Actual active frames

[SourceNameFrameEmbedding.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameFrameEmbedding.lean)
proves that ground term/process embedding, every finite active-frame entry,
`activeFrame`, `frameProcess` and `capture` commute with name mapping. Active
variable domains remain unchanged; both names and values move in their own
sorts. `frameProcess_reduction_mapNames_iff` specializes extended internal
equivariance to actual frame/process states. `frame_capture_mapNames` retains
the entire shifted old frame and complete fresh output before canonical handle
renaming. These laws reuse the existing source rules.

## Controls and limits

[SourceNameFrameSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameFrameSPOT.lean)
contains ten kernel controls. Independently written frames retain the old public
key and the full new secret value. A compound public recipe evaluates its opaque
key handle correctly. The leaking output remains operationally possible and
observable after renaming; replacing its value with a public literal is
distinguishable using a public equality test. The actual reached election
observation theorem also transports.

The renamed private policy blocks visible output on the renamed private channel;
keeping the old policy admits it. Private internal communication still runs.
An explicitly written extended frame verifies active values/domains, and a
compound input checks actual binding after evaluation. These are structural
proofs and kernel controls, with no new randomized cryptographic campaign and
no secrecy inference from blocked attacks.

Reuse the [global name-permutation laws](helios-source-name-permutations.md),
[variable well-formedness](helios-source-wellformed.md) and
[stage matching](helios-process-stages.md) when adding actual name scope/alpha,
outer voter construction and the full source converse. The maintained
[blueprint](helios-proof-blueprint.md) records the remaining bisimilarity and
symbolic secrecy obligations.

Integrated verification for the renamed-observation checkpoint: `lake build` passes **3841 jobs**, with
**2908** nonempty standard-only and **47** axiom-free reports. The claim audit
covers **1969** public theorem entries and **89** current-status documents.
All six changed Lean sources have current oleans; **1098** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-renamed-observations-full-build.log`.
This increment adds 28 theorem audits, including ten kernel controls, and three
definition checks. Targeted controls pass 1217 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-renamed-observations-verification.txt`.
