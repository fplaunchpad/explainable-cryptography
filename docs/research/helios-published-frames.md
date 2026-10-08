# Published partial and result frames

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: **machine-checked frame construction and equivalence reduction**.
The actual final frames now retain the initial observations and publish every
candidate's partial decryption and result. The result tuple is a public
computation from the partial frame. Consequently final-frame static equivalence
is equivalent to partial-frame static equivalence. **That partial-frame
equivalence remains unproved**, so B8 remains open. See the maintained
[blueprint](helios-proof-blueprint.md).

## Observation layout

[PublishedFrames.lean](../../ExplainableCrypto/Helios/Symbolic/PublishedFrames.lean)
uses `Frame.extend` to append one value while preserving every old handle.
`candidateTuple` contains all `n+1` fields in order, followed by the existing
bottom terminator. It uses the tuple output shape of the source's BB6/BB7 and
φ6/φ7 observations (Cortier–Smyth Appendix B, paper pages 48–51).

| Handle | Initial frame | Partial frame | Final frame |
| --- | --- | --- | --- |
| 0 | Election public key | Same value | Same value |
| 1 | First honest ballot | Same value | Same value |
| 2 | Second honest ballot | Same value | Same value |
| 3 | Absent | Complete candidate partial-decryption tuple | Same value |
| 4 | Absent | Absent | Complete candidate result tuple |

Each partial is the actual term `partialDecrypt secret tallyCiphertext`.
Each result is `dec tallyPartial tallyCiphertext`, using the whole matching
candidate aggregate. Public submissions remain the same initial-frame recipes
in both worlds, as in the [shared tally theorem](helios-shared-tallies.md).
The restriction set is unchanged and still includes the election secret.

[FrameExtension.lean](../../ExplainableCrypto/Helios/Symbolic/FrameExtension.lean)
proves exact old-handle retention, public recipe lifting,
unchanged evaluation of lifted recipes, and complete tuple projection and
substitution laws. The control for a missing last partial distinguishes the
truncated tuple under full E, not just syntactically.

## Public reconstruction of results

[PublishedResults.lean](../../ExplainableCrypto/Helios/Symbolic/PublishedResults.lean)
defines the proof obligations for the actual frame values. `resultRecipe`
projects each partial from handle 3 and decrypts the corresponding lifted
public tally recipe. `resultRecipe_public` requires only public submissions;
`resultRecipe_value` proves that its evaluation equals the exact result tuple.
Neither result assumes accepted submissions, matching numeric tallies or
initial static equivalence.

The generic `Frame.StaticEq.extend_public_iff` proves that appending values
E-equal to the same public recipe adds no equality observations and retains all
old ones. Instantiating it gives:

```lean
theorem final_frame_staticEq_iff_partial (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) :
    Frame.StaticEq (finalFrame ns false left right rs)
      (finalFrame ns true left right rs) ↔
    Frame.StaticEq (partialFrame ns false left right rs)
      (partialFrame ns true left right rs)
```

This is an exact reduction, not an assertion that either frame pair is
equivalent. `final_result_numeric` separately places the previously proved
numeric tally at each actual final result slot for accepted submissions.

## Why partial publication is still an obligation

`initial_secret_partial_not_deducible` proves that no public initial-frame
recipe can reconstruct `partialDecrypt secret binding`, for any binding.
Otherwise a minimum partial-value recipe would expose a public argument
deducing the restricted election secret. The initial static-equivalence
theorem therefore cannot handle this publication by public postprocessing.

The independently derived control `equal_tally_individual_partial_leak`
keeps the honest total equal to one in both worlds but publishes an individual
ballot's partial instead. The same public recipe then returns zero before the
swap and one afterwards, refuting static equivalence of those altered frames.
This does not attack the defined aggregate-partial protocol; it refutes the
tempting claim that equal tallies justify arbitrary partial publication.

The remaining B8 theorem must prove static equivalence of the **defined
aggregate partial frames**, under fresh names, valid honest candidates and
accepted public submissions. It must cover all recipes using the new tuple,
including ciphertext binding comparisons, E6 results and structured terms used
as E5 secret keys. Initial-frame minimum origins do not apply unchanged to
the new handles. Historical process matching and the top-level secrecy
theorem also remain open.

## Controls and verification scope

[PublishedFrameSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/PublishedFrameSPOT.lean)
contains eight controls: arbitrary old recipe retention; both candidate slots
with independently expected zero/one results; rejection of an omitted partial
slot; a public result recipe on a nonempty submission list; the actual result
slot equal to two with its voter-count bound; an inhabited diagonal criterion
with distinct public names; the individual-partial leak despite equal totals;
and non-deducibility of the actual trustee partial in the initial frame.

[PublishedFrameExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/PublishedFrameExperiments.lean)
detects unsafe individual publication and an omitted last candidate at input
0, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 cases, size 40,
`gaveUp=0`; 2048 deterministic inputs pass. The generated scope covers one and
two candidates, zero through five submissions, nonliteral honest candidates,
both assignments, retained handles, tuple reconstruction and independently
counted results. Raw normalization is used only on the generated cases; it is
not a full-E decision procedure. Gate log:
`tmp/variable-overlap/published-frame-gate.log` (1001 jobs).

No top-level milestone is promoted. Coverage remains seven of ten (70%
unweighted); all twelve initial-frame operator cases remain complete.

Integrated evidence: full `lake build` passes **3617 jobs**. The claim checker
covers **829 public theorem entries** and **46 current-status documents**.
The full log contains **1795 nonempty standard-only axiom reports** and **20
axiom-free reports**. This increment adds thirty public theorem audits, eight
SPOTs and six definition checks. Log:
`tmp/variable-overlap/published-frame-full-build.log`.
