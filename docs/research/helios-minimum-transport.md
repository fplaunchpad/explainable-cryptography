# Lifting minimum observations to arbitrary recipes

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked, conditional**. The generic lifting theorem now
connects minimum-pair observation steps to static equivalence of arbitrary
public recipes, provided every recipe has a shared minimum representative.
The subsequent [observation assembly](helios-observation-assembly.md) proves
the historical minimum step under reverse shared minimization. Shared
minimization in both directions remains open for the swapped historical frames.


The [local-root closure](helios-local-root-transport.md) now proves that minimum
children give minimum parents for constructed keys, partial constructors,
proofs and semantically stuck destructors. These roots are their own shared
representatives. The remaining transport interface requires new witnesses only
for nonminimum roots with minimum children: successful destructors, pairs,
ciphertext constructors and arithmetic. Those cases remain open in both swaps.

## What a shared minimum requires

`Frame.SharedMinimum φ ψ r` supplies one recipe `m` that is minimum among all
public recipes with its source value, with both equalities
`EqE (φ.eval r) (φ.eval m)` and `EqE (ψ.eval r) (ψ.eval m)`.
`Frame.CommonMinima φ ψ` requires this for every public `r` under the same
restricted-name policy and handle domain. Source-minimum existence alone
supplies only the first equality.

`Frame.MinimumObservationStep φ ψ` is the assembled minimum-pair branch:
for any two source-minimum recipes, preservation of all strictly smaller
public equality tests implies preservation of their equality test.
The subsequent constructor/destructor assembly derives this step for the
historical frames from reverse shared minimization; the definition alone does
not discharge its hypotheses.

`Frame.staticEq_of_common_minima` proves that these two premises imply
`Frame.StaticEq φ ψ`. Its strong induction uses the total size of the two
recipes. If replacing them by their shared minima reduces the total, the
induction hypothesis applies to the representatives. If the total does not
shrink, each original recipe is itself minimum, so the minimum-pair step
applies directly. The proof retains both directions of equality preservation.

The theorem covers arbitrary public syntax and every frame with the fixed
policy and handle domain. It changes no cryptographic equations or attacker
operations. Its frame-specific premises are substantive remaining obligations.

## A local minimization obligation

`Frame.MinimumChildren φ r` requires only the immediate children of `r` to be
source-minimum. `Frame.LocalMinimumTransport φ ψ` requires a shared minimum
for every public recipe satisfying that condition; the root may be nonminimum.
`Frame.common_minima_of_local` proves that this local obligation supplies
`CommonMinima` by structural induction: replace each child by its shared minimum,
use congruence in both worlds, then minimize the root.

`Frame.staticEq_of_local_minimum_transport` combines that structural argument
with the total-size observation induction. The historical observation assembly
now removes the branch-assembly obligation under reverse shared minimization.
The remaining sufficient target is local root minimization in both orientations.
The existing smaller-observation premise cannot silently discharge that target.

Two additional interfaces clarify the boundary:

- `SharedMinimum.of_recipe_eqE`, `.of_raw_reduces` and
  `.of_raw_normalization` transport equality before substitution to both worlds.
  The raw normalizer result must actually be source-minimum; raw normality alone
  is insufficient.
- `CommonMinima.minimum_destination` uses common minimization in the reverse
  direction to carry a source minimum to the destination. `StaticEq.common_minima`
  proves necessity of shared transport; using it to establish the premise of
  the lifting theorem would be circular.

## Checked obstacles and controls

The finite size/equality countermodel uses four recipes with sizes `[1,1,2,1]`,
source values `[0,1,0,2]`, and destination values `[0,1,1,2]`. All source-minimum
pairs agree across worlds, so the conditional minimum-pair step holds. Recipes
0 and 2 nevertheless change from equal to unequal. No shared source minimum
exists for recipe 2. This refutes dropping shared transport from the abstract
inference; it is not a Helios privacy attack.

A destination mapping all recipes to 0 provides the companion countermodel:
shared minima exist, but the minimum step and static equivalence fail.
An injective renaming of the source values passes both premises and all tests,
retaining distinct observations and a strictly nonminimum recipe.

The size-budget control uses actual public recipes in a frame with no handles:

```text
minimum = pair(name40, name41)                 size 3
child   = pair(fst(pair(name40, bottom)), name41) size 6
parent  = fst(child)                          size 7
output  = name40                             size 1
```

`literal_pair_minimum` excludes every size-one/two competitor under full E.
`child_comparison_exceeds_budget` proves both relevant evaluation equalities
and the exact counts: comparing child to minimum costs 9, whereas comparing
parent to output costs 8. The child is strictly smaller than its parent.
This is an induction-budget obstruction; the parent/output equality itself is
preserved by an ordinary rewrite in every frame.

An additional actual-frame control exposes name70 in one world and name71 in
the other. A public raw wrapper around name40 has a shared minimum in both,
but the handle/name70 observation distinguishes the frames. A diagonal instance
of the complete local lifting theorem retains unequal public names; it is not
a different-vote privacy proof.

## Reproduction and scope

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/MinimumTransportExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/minimum-transport-full-build.log
```

The two deliberately broken gates fail at input 0, seed 1, zero shrinks.
The finite lifting check passes seeds 1, 7 and 42, with 500 configured cases
per seed, maximum size 40 and `gaveUp=0`. Its deterministic backstop exhausts
4096 models: all four-recipe binary source/destination maps and all size maps
using sizes 1 or 2. The implication is checked directly without discarded
samples. This tests the abstract inference, not a full-E equality procedure.
The kernel-checked theorem supplies the unbounded result under its premises.

The new modules are `MinimumTransport`, `LocalMinimumTransport`,
`MinimumTransportExperiments` and `MinimumTransportSPOT`. `Audit.lean` checks
19 new public theorem types and axiom sets, including eight controls, and five
definition interfaces. The full `lake build` passes (3529 jobs), with 1452
nonempty axiom reports using only `propext`, `Classical.choice` and `Quot.sound`,
and 17 axiom-free reports. No warnings, errors or `sorryAx` occur. The claims
checker covers 483 public theorem entries and 26 current-status documents.
Build evidence is recorded in the
[results ledger](helios-results.md#arbitrary-recipe-lifting-enquiry).

Trusted definitions remain E/E0, publicness, evaluation, size minima, and
static equivalence. The independent mathematical fixtures test the inference
and source/destination equality boundary. They do not validate a concrete
cryptographic implementation. See the [static-equivalence record](helios-static-equivalence.md)
and [multiplication branch](helios-multiplication-observations.md) for the
existing frame-specific work. Final frames publishing partial decryptions,
process matching, and ballot secrecy remain open in the canonical task list.
