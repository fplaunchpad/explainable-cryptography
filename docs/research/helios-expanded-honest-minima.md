# Honest ciphertext minimum size after publication

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: machine-checked. Current milestone: [B8](helios-proof-blueprint.md).
Every nonempty combination of honest ciphertext selectors remains globally
minimum in the actual expanded published frame, assuming fresh names, public
submissions and numeric published results. Accepted submissions supply the
numeric premise. The theorem considers all public recipes over all handles.

## Reuse the existing honest computation

[`combinationRecipeWith`](../../ExplainableCrypto/Helios/Symbolic/CombinationHandleTools.lean)
substitutes an explicit handle map into the existing `combinationRecipe`.
It introduces no new ciphertext algebra. The exact old-handle evaluation
lemma reuses the initial homomorphic value theorem in the expanded frame.

A selector at index `j` costs `j + 2` syntax nodes. Renaming handles preserves
this cost. For a nonempty product tree, its size plus one is the sum of
`j + 3` over its indexed occurrences. Reassociation and permutation retain
this sum; repeated indices are counted repeatedly. An assembly grouped as
honest has exactly the recorded selector-tree syntax.

## Compare every public competitor

[`expanded_minimum_honest_combination_origin`](../../ExplainableCrypto/Helios/Symbolic/ExpandedHonestMinima.lean)
starts with any globally minimum public recipe equal under full E to an
honest combination. Numeric published-value origins recover its exact
ciphertext assembly. The existing opaque group comparison excludes both
constructed and mixed groups. Fresh nonce identity then forces the same
indexed occurrence bag as the supplied combination.

`expanded_minimum_honest_combination` chooses a global minimum competitor
and applies this origin theorem. Its occurrence bag fixes its exact size,
proving that the original combination is itself globally minimum.
`accepted_expanded_minimum_honest_combination` discharges numeric origins
from accepted public submissions. Publicness and freshness remain explicit.

`expanded_honest_combination_shared` uses that source minimum as the shared
recipe with any destination of the same policy and handle type. This does not
assert equal ciphertext values between worlds; each original recipe equals
itself within its own world. No smaller-observation or smaller-minimum
premise is required for this branch.

`expanded_nonminimum_ciphertext_product_public_group` classifies a
ciphertext-valued product whose children are minimum but whose parent is not.
It returns exact assemblies for both children, a public parent recipe and a
constructed-or-mixed group. The honest case is excluded by the global minimum
theorem. Combined with the checked [constructed product
transport](helios-expanded-constructed-minima.md), this leaves mixed products
as the remaining ciphertext multiplication case.

## Controls and bounded checks

The [executable gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedHonestExperiments.lean)
detects three deliberate defects at input zero, seed 1, zero shrinks: counting
every selector as two nodes, deleting a repeated nonce occurrence, and treating
a projection of a published partial as an honest ciphertext. Seeds 1, 7 and
42 each pass 500 cases at size 40 with `gaveUp=0`. All 2048 deterministic inputs
pass in both swaps, with one through eight selectors, both voters and candidate
indices, and repeated occurrences. An independent list calculation predicts
syntax size and nonce multiplicity. The executable view uses raw normalization
and nonce leaf bags; it is not a complete E decision procedure or minimum-size
proof.

Eight [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedHonestSPOT.lean)
cover distinct reassociations with exact ten-node global minima and shared
syntax; duplicate retention at five nodes; arbitrary minimum competitor
origins and costs; exclusion of every whole handle alias; an eight-node
minimum after nonempty accepted submissions; failure with colliding nonces;
failure when a result slot is replaced by the honest ciphertext product; and
an inhabited nonminimum-product classification with minimum children.
Different-vote controls use the existing nonliteral vote fixtures.

The arbitrary-publication countermodel is a modified frame, explicitly
outside the actual publication specification. It shows why one cannot infer
preservation of minimum size under unrestricted frame extension. The actual
partial and numeric result handles satisfy the stronger origin/protection
facts used in the theorem.

## Remaining frontier

Mixed ciphertext products, remaining local/selector and successful-case
shared transport, and the simultaneous global shared-minimum induction remain
open. B8 final-frame equivalence, B9 process matching and B10 full symbolic
secrecy are incomplete. Coverage stays seven of ten milestones (70% unweighted,
not an estimate of effort or time remaining). The [results
ledger](helios-results.md) records integrated build and axiom evidence.

Integrated verification: full `lake build` passes 3725 jobs, including eighteen
new public theorem audits and all eight kernel controls. The log contains 2259
nonempty reports using only `propext`, `Classical.choice` and `Quot.sound`, plus
21 axiom-free reports. The claim checker covers 1294 public theorem entries and
68 current-status documents. Log: `tmp/variable-overlap/expanded-honest-full-build.log`.

[Expanded mixed compression](helios-expanded-mixed-compression.md) now closes
mixed products with at least two public constructors under two-way smaller
minima. Minimum mixed competitors have exactly one constructor and preserve
honest indices, public nonce equality and zero-padded payload equality. The
remaining mixed case needs global padded payload minima with published numeric
handle costs.

[Expanded padded minima](helios-expanded-padded-minima.md) now close the general
one-constructor mixed case using published numeric-handle costs and shared
padded values. All multiplication local cases are assembled under the two
smaller-minimum hypotheses. Remaining pair/selector and successful-case
transport and the global simultaneous induction stay open.

[Expanded successful-check transport](helios-expanded-successful-checks.md) now
closes `checkspk`, retaining whole-ciphertext binding and exact honest combination
origins. The remaining local interface for all three frame presentations is
successful decryption in both directions; B8 local coverage is now 11/12.

[Result-handle realization](helios-result-handle-binding.md) now transfers full
tally bindings for all public old-plus-results recipes, including nested uses,
without size or minimum hypotheses. Only minimum ciphertexts without a
result-only presentation remain in the trustee-binding callback. A checked
ten-node minimum result-nonce recipe refutes old-only syntax and grows to
fourteen nodes under numeral realization.
