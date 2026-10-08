# Minimum honest ciphertext products

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. Every nonempty combination of fresh honest
ciphertext selectors is globally minimum among all public recipes in the
initial historical frame. The theorem covers every positive candidate count,
both assignments and valid ground vote representations, including abstention
and nonliteral E-equivalent bits. The unchanged recipe is a shared minimum in
every destination frame under the same full restriction.

## Reuse the existing homomorphic and provenance results

This proof uses the existing `combination_value` homomorphic theorem,
`minimum_ciphertext_grouping` origin theorem and
`CiphertextGroup.components_eq_iff` provenance classification. No homomorphic
equation, ciphertext representation or rewrite relation is added or changed.

`CiphertextAssembly.recipe_of_honest_group` proves that an assembly grouped as
honest is exactly the recorded combination of selectors. Grouping cannot erase
a public constructed contribution.

`combinationRecipe_nodeCount` computes exact occurrence cost: a selector at
candidate position `j` costs `j+2`, so the whole product's node count plus one
is the sum of `j+3` over its indexed occurrence bag. This retains every repeated
selector and accounts for all multiplication nodes.

`minimum_honest_combination_origin` classifies an arbitrary minimum equivalent.
Nonce provenance excludes constructed and mixed groups; freshness fixes the
honest index bag exactly. `combinationRecipe_nodeCount_eq` then fixes the whole
recipe cost. Comparing against that arbitrary minimum proves
`minimum_honest_combination`. `honest_combination_shared` uses the original
minimum syntax in every destination; this does not say the two frames are
statically equivalent.

`nonminimum_ciphertext_product_public_group` handles the remaining local
situation: a ciphertext-valued product with minimum children but a nonminimum
parent has an exact public coherent assembly whose group is constructed or
mixed. The honest-only case is excluded by a proved minimum-size theorem,
rather than by restricting the adversary.

## Controls, scope and frontier

Seven SPOTs retain distinct reassociated ten-node minima with repeated indexed
selectors, observable duplicate products with five-node minima, exact minimum
competitor origins/costs, the one-candidate eight-node case, failure with
colliding nonces, failure after publishing a whole product as another handle,
and a real remaining product with a public constructed contribution.

The pre-proof gate detects nonce-collision and duplicate-erasure defects at
input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 pass 500 configured cases each,
size 40, gaveUp=0; all 2048 deterministic inputs pass. Inputs cover one through
five candidates, one through seven occurrences, honest assembly reconstruction,
exact indexed costs and normalized selector leaf values in both assignments.
It does not decide global minimum size or arbitrary full-E equality.
Log: `tmp/variable-overlap/honest-product-minimum-gate.log`.

The [results ledger](helios-results.md#honest-only-ciphertext-product-minimum-result)
records the full build and axiom audit. The [blueprint](helios-proof-blueprint.md)
remains at B7-M, with nine of twelve operator cases and six of ten top-level
milestones closed. Subsequent [joint induction](helios-joint-minimum-transport.md)
discharges constructed-only products inside the reduced static criterion. Mixed
honest/public products still need shared minimum representatives. Successful decryption/checking, final transcript equivalence,
process matching and symbolic ballot secrecy also remain open.

The [expanded honest minimum theorem](helios-expanded-honest-minima.md) now
reuses this syntax, indexed cost and homomorphic value result after actual
publication. Opaque group comparisons and numeric origins justify global
minimum size against recipes using the new partial/result handles. Arbitrary
frame extensions still need not preserve minimum size.
