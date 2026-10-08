# Result-handle realization and full tally binding

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: machine-checked reduction; integrated build and audit complete. Every public
recipe using retained old handles and numeric result handles now has a shared
public initial recipe. Its full equality observations and complete tally binding
transfer through B7. The remaining borrowed-E6 obligation concerns minimum
ciphertexts without such a result-only presentation. B8 stays 11/12 locally;
B8, B9 and B10 remain open and top-level coverage stays 7/10 milestones.

[ResultHandleSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/ResultHandleSyntax.lean)
defines a derived presentation with three retained handles and one result slot
per candidate. `resultEmbedding` maps these slots into the actual expanded
frame. It omits trustee-partial slots; it does not change the protocol or its
public transcript. `resultNumeralRecipes` maps each result to its known public
numeral and retains each old variable. Zero is a one-node constant, never an
empty recipe. Substitution preserves the public-name policy in both directions
for the handle embedding and preserves publicness for numeral realization.

[ResultHandleTransport.lean](../../ExplainableCrypto/Helios/Symbolic/ResultHandleTransport.lean)
proves `result_recipe_value` by full-E pointwise equality and substitution
through every operator. `accepted_result_recipe_common_initial` uses the shared
numeric tally theorem to select one table of numerals for both assignments.
It gives one public initial recipe for each arbitrary nested result-only recipe,
with no minimum or recipe-size premise.

`accepted_result_frame_staticEq` proves unbounded static equivalence for this
derived old-plus-results frame. `accepted_result_recipe_tally_binding_swap`
compares the realized initial recipe with the entire public initial tally
recipe, using B7. This is complete ciphertext binding; equal numeric totals
alone do not prove it. `accepted_result_recipe_bound_tally_shared` supplies the
actual one-node result-slot representative of the corresponding borrowed E6
decryption. Neither theorem requires minimum size or smaller observations.

`accepted_expanded_trustee_binding_of_remaining_recipes` connects this result
to the existing `ExpandedTrusteeBindingTransport` interface. Its remaining
callback is invoked only for minimum ciphertext recipes with no result-only
syntactic presentation. The original two strict smaller-minimum hypotheses
and the original decryption bound are unchanged. Both resulting directions
feed the already checked expanded/partial/final conditional equivalence
pipeline. The remaining callback is not proved here.

A possible next route is to exclude trustee-partial occurrences from minimum
full-tally matches. That is a new structural conjecture, not a consequence of
name non-deducibility or these result-only theorems. It must allow numeric
result handles: the counterexample below disproves the stronger old-only
syntax claim. It must also account for constructors that hide partial values,
minimum origins of destructors, and homomorphic key sharing.

[ResultHandleExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ResultHandleExperiments.lean)
tests one through five candidates, both assignments, old handles and zero/one
result slots through addition, pairing, encryption, proof constructors,
projection, direct E5, constructed E6 and proof checking. The first raw-only
comparator failed at input zero. This was an oracle limitation: raw normalization
does not canonicalize all numeric E0 equalities. The failure is retained as a
negative control. The revised fixture comparator simplifies purely numeric
additions recursively and then performs raw reductions; it preserves zeros next
to nonnumeric atoms. This remains a bounded fixture oracle, not a complete E/E0
decision procedure. Formal value proofs use full E directly.

Mapping every result to zero, erasing trustee partials to bottom and treating
raw normalization as a full numeric comparator each give the intended input-zero
failure at seed 1, zero shrinks. Seeds 1/7/42 each pass 500 revised cases at size
40 with `gaveUp=0`; all 2048 deterministic inputs pass. The gate build passes
1109 jobs; syntax builds in 993 jobs and transport in 994 jobs.

[ResultNonceSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ResultNonceSPOT.lean)
checks a nonempty accepted election with a public adversarial nonce represented
by two ones and an extra vote of one. Its published tally is two. That result
handle can supply the adversarial nonce of a globally minimum ten-node mixed
ciphertext matching the entire tally in both assignments. The new binding
transport gives the shared result-slot decryption. This minimum recipe has no
retained-old syntactic preimage. Replacing its result handle with `addNumeral 2`
increases its raw size to fourteen nodes. Thus value realization neither
preserves minimum size nor permits assuming old-only minimum origins.

[ResultHandleSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ResultHandleSPOT.lean)
adds nested zero/one realization, a real result of two inside a public-key
constructor, unbounded result-frame equivalence with distinct ballot values and
public-name observations, the minimized raw comparator failure, rejection of
trustee-partial erasure, and an inhabited remaining-callback/final-frame pipeline.
Together the two modules have nine kernel controls. The pipeline uses equal
candidates and does not claim arbitrary-candidate B8; the result-only equivalence
and nonce-binding controls cover different candidate assignments. All controls
build in 1130 jobs. Remaining initial failures were elaboration/publicness and
unused simp arguments, fixed without weakening the claimed reduction.

See the [proof blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and
[preceding trustee-binding checkpoint](helios-expanded-public-decryption.md).

Integrated evidence: full `lake build` passes 3756 jobs. Twenty-four new
public theorem audits give 1424 covered entries across 74 current-status
documents. The log contains 2389 nonempty reports using only `propext`,
`Classical.choice` and `Quot.sound`, plus 21 axiom-free reports. All seven
changed Lean modules have current oleans, with no proof holes or custom axioms.
All 951 local links resolve; the log has no warnings/errors and
`git diff --check` passes. Log: `tmp/variable-overlap/result-handle-binding-full-build.log`.
