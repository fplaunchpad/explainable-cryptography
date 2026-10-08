# Minimum nonce compositions

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. In the initial historical frame, a composition
with minimum children is minimum. The theorem covers every positive candidate
count, valid ground substitutions, either assignment and any caller name
restriction. It requires neither freshness nor smaller-observation preservation.

## Count every leaf occurrence

`Term.composeLeaves_nodeCount` proves that the sum of raw leaf sizes plus the
number of leaves equals the whole recipe's size plus one. A binary composition
tree with `k` leaves has `k-1` composition nodes. Duplicate occurrences each
contribute their full cost; no unit or idempotence equation is introduced.

`MinimalRecipe.compose_leaf` transfers minimum size to every outer composition
leaf through its actual syntax context. `minimum_leaf_cost_bags_eq` proves
that two bags of minimum recipes with the same substituted full-E class bag
have the same node-count bag. Each matched pair is minimum in the same source
world, so its two sizes bound each other. This is a one-way accounting result;
equal sizes alone do not imply equal values.

`Term.nodeCount_eq_of_compose_leaf_costs` recovers equality of whole recipe
sizes from equality of those leaf-cost bags, including the occurrence counts.

## Close the minimum-size argument

`minimum_compose_leaves_atomic` uses the initial-frame origin theorem: a minimum
recipe with a composition E-value must have raw compose syntax. An outer raw
leaf has no such syntax, so its evaluated value is semantically indivisible
under composition. This source-world result preserves any caller name policy
and has no observation or freshness premise.

`minimum_of_compose_leaves` chooses a minimum equivalent of the recipe.
Both recipes have semantically indivisible minimum leaves. Full-E composition
factor equality therefore supplies matching bags of substituted leaf classes.
The equal-cost theorem and exact syntax accounting show that the original
recipe has the same size as its minimum equivalent. It is consequently minimum.

`minimum_compose_of_children` derives the leaf premises from its two minimum
children. The source recipe is then its own shared minimum in any destination
frame under the same policy. This does not state that its value is unchanged
between different vote assignments.

The scope remains the actual initial historical frame. A frame directly
publishing a composed value can supply a shorter handle and invalidates this
minimum-parent claim, even when its literal children are minimum.

## Four remaining local cases

`Frame.DecryptCheckAddMulTransport` retains successful decryption, successful
proof checking, addition and multiplication for nonminimum roots with minimum
children. `destructor_arithmetic_transport_of_four_cases` supplies composition
to the preceding interface. `staticEq_of_decrypt_check_add_mul_transport`
derives initial-frame static equivalence if these four cases have shared minima
in both orientations. The criterion still requires fresh names through earlier
projection and pairing results. Its two different-vote premises remain unproved.

## Controls and reproducible evidence

Seven public SPOTs retain:

- Reassociation and permutation of two repeated four-node key leaves and a
  one-node ballot handle. Both distinct recipes are eleven-node minima;
  three leaves contribute nine nodes, and composition contributes two.
- Three-node minimum compositions containing zero or repeated names, with
  full-E proofs that neither zero nor the repeated occurrence disappears.
- A weaker caller policy permitting the secret-key name, in a frame with
  colliding honest nonces. The recipe is minimum under that policy and is not
  public under the full restriction.
- A removable wrapper refuting closure without minimum leaves.
- A frame directly publishing a composed value, giving a shorter handle despite
  minimum literal children.
- An actual nonminimum addition of two minimum zeros, retaining a remaining
  case and its shared literal-zero representative.
- A diagonal instantiation of the reduced criterion with distinct public names.
  This does not prove different-vote static equivalence.

The pre-proof Plausible gate detects the zero-unit and duplicate-collapse
defects at input 0, seed 1, zero shrinks. Positive checks preserve exact raw
leaf costs, multiplicities and permutations with non-atomic key, stuck-projection
and ciphertext leaves. Seeds 1, 7 and 42 pass 500 configured cases each,
size 40, `gaveUp=0`. All 2048 backstop inputs pass with one through seven leaves
and both swaps.

The executable check compares bags of normalized raw evaluated leaves.
It does not decide full-E quotient equality or establish minimum size. An
initial harness attempted quotient equality and failed because no executable
decision procedure exists; the successful gate and general proof keep those
roles separate. The proofs use full-E classes only for metatheory accounting.

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/CompositionMinimumExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/composition-minimum-full-build.log
```

The five new modules are `CompositionMinimumCosts`, `CompositionMinimumClosure`,
`DecryptCheckAddMulTransport`, `CompositionMinimumExperiments` and
`CompositionMinimumSPOT`. The audit checks sixteen public theorem types and
axiom sets, including seven controls, plus three definition interfaces.
The full build passes (3560 jobs), with 1563 nonempty axiom reports using only
propext, Classical.choice and Quot.sound, and 18 axiom-free reports. No warnings,
errors or sorryAx occur. The claims checker covers 595 public theorem entries
and 33 current-status documents. The [results ledger](helios-results.md#composition-minimum-closure-enquiry)
records full build and axiom evidence.

Trusted definitions remain EqE/E0, source frames, public recipes, raw leaves,
full-E factor classes, minimum node count and SharedMinimum. The independent
semantic reference is composition's exact AC theory without a unit or duplicate
collapse. No cryptographic equation, public operation or custom axiom changes.
The four local cases above, final public partial-decryption frames, historical
process matching and full ballot secrecy remain open in the
[task list](../../task%20list.md).
