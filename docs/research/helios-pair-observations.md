# Pair-valued equality observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Every minimum pair-valued public recipe in the actual
initial frame is a constructed pair or a nonempty projected ballot tail.
Equality between these forms transfers across swaps under the existing
`Frame.ObservationsBelow` premise. This closes the pair-valued branch of the
minimum-recipe argument; the global premise and full static equivalence remain
open.

The result covers all positive candidate counts and all valid ground candidate
representatives, including reducible terms. The final interface requires fresh
names and the full restricted-name policy. The origin theorem permits an
arbitrary caller policy and does not require freshness.

## Exact origins and tail equality

[PairObservationOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/PairObservationOrigins.lean)
refines the existing minimum pair origin into `Historical.General.PairObservationForm`:

```text
r = pair(a,b), or
r = snd^k(var(i+1)), where i is one of the two voters and k < fieldCount(n).
```

The strict bound guarantees a nonempty ballot suffix. The public-key handle and
its projection chains cannot have pair values. Every other pair-valued handle
chain is exactly an in-range ballot tail. This classification retains raw
recipe syntax, rather than merely an equivalent replacement recipe.

`ballot_tail_recipe_value` supplies the actual E-value of a tail through and
including the empty position. `ballot_tail_pair_value` uses the strict bound
to prove pair-valuedness. Thus `PairObservationForm.pair_value` proves that the
classified syntax is pair-valued in either swapped world. It does not transport
arbitrary evaluations or assume that minimum size is preserved after a swap.

Full-E tuple equality preserves the number of pair cells, even with reducible
or pair-valued fields. `EqE.tuple_length` proves this by ordered pair injectivity
and separation of pairs from bottom. `EqE.tuple_get` transfers equality at any
common in-range field position.

For two nonempty ballot tails, the remaining lengths first identify their
original offsets. Each suffix retains the aggregate proof at its final field.
Equality of that field then identifies the voter by fresh aggregate nonce
provenance. `ballot_tail_equality_iff` therefore states:

```text
EqE(eval(snd^k(var(i+1))), eval(snd^l(var(j+1)))) iff i = j and k = l
```

Both offsets must be below `fieldCount n`, and `Names.Fresh` is explicit. Empty
tails of different voters both reach bottom. Colliding nonces can make entire
nonempty ballots equal when their candidate values agree. The checked controls
retain both failures of weakened versions of the criterion.

## Comparisons involving constructed pairs

[PairObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/PairObservationInduction.lean)
uses actual pair-valuedness to reconstruct a term from its two projections.
`pair_equality_iff_projections` characterizes equality of `pair(a,b)` with a
pair-valued term `t` by the two ordered comparisons:

```text
a =E fst(t), and b =E snd(t).
```

This is a conditional consequence of the existing equations. No global pair eta
equation is added; the reconstruction is false for an arbitrary public name.

When `t` is a recipe `s`, the first comparison has size `|a| + 1 + |s|`,
strictly less than `1 + |a| + |b| + |s|` because `|b| > 0`. The second comparison
is smaller because `|a| > 0`. Both projections remain public. These bounds work
even when `s` is a long ballot-tail recipe.

`constructed_pair_equality_transfer` handles constructed/constructed and
constructed/tail comparisons using those two smaller tests. It retains an actual
pair value for `s` in each frame. `pair_form_equality_swap` derives these values
from the forms, uses symmetry for tail/constructed comparisons, and uses the
exact tail identity criterion for tail/tail comparisons.

`minimum_pair_equality_swap` derives both forms from two first-world minima and
their supplied pair E-values. Its final statement assumes neither second-world
minimum size nor a caller-supplied origin certificate. The smaller-observation
hypothesis remains explicit at the sum of the original recipe sizes.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Tuple equality preserves length and fields | machine-checked | `EqE.tuple_length`, `EqE.tuple_get` | Full E, arbitrary fields, valid common index |
| A pair-valued handle chain is an exact nonempty ballot tail | machine-checked | `General.frame_projection_pair_origin` | All three initial handles, arbitrary valid candidate assignments |
| Minimum pair-valued syntax has two forms | machine-checked | `General.minimum_pair_observation_form` | Minimum size, actual initial frame, supplied pair value |
| Tail equality identifies voter and offset | machine-checked | `General.ballot_tail_equality_iff` | Fresh names and two nonempty tails in one world |
| Constructed pairs compare through smaller projection tests | machine-checked | `constructed_pair_equality_transfer` | Public arguments, pair-valued other recipe in both frames, bounded hypothesis |
| The minimum-pair branch transfers equality | machine-checked | `General.minimum_pair_equality_swap` | First-world minima/values, freshness, full policy, bounded hypothesis |

## Independent controls and executable scope

[PairObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/PairObservationSPOT.lean)
contains nine theorem controls. The exact tail criterion is instantiated at every
nonempty offset of the two-candidate fixture in both swaps. Empty tails from
distinct voters reach literal bottom; colliding nonces refute the fresh voter
criterion on whole nonempty ballots.

At one candidate, component and aggregate proof fields coincide, but tails
starting at those fields remain unequal because their lengths differ. A public
constructed pair rebuilds the entire ballot from its two projections, while
replacing its second member by bottom changes the value. A public name refutes
unconditional pair eta. A projection wrapper around a ballot handle has its
pair value but lies outside both exact forms and is not minimum.

The full minimum-pair interface is inhabited in the actual different-vote
worlds by two unequal one-node ballot handles. Its total size bound is two;
no public recipe comparison has a smaller total size. This is a checked base
case, not a proof that the bounded premise holds at larger sizes. Separate
controls instantiate constructed/constructed and both mixed orientations under
diagonal candidate assignments. Public names 40 and 50 retain their ordered
inequality, and the reconstructed ballot remains a positive equality control.

`PairObservationExperiments.lean` first detects the omitted-nonempty mutation
at input 0, seed 1, zero shrinks. Both positive gates pass seeds 1, 7 and 42,
each with 500 configured cases, size 40 and `gaveUp=0`, plus 256 deterministic
inputs. A 6760-input directed sweep covers all nonempty offset pairs and all
voter pairs at counts one through five and both swaps; the encoding repeats
some combinations. The candidate assignments are left abstention and right
selection of candidate zero.

The constructed-pair gate checks reconstruction from both projections, changed
second members, and strict comparison-size bounds. Its expected tail equality
uses voter/offset identity and its truncation outcome uses the independently
specified final-field position. These raw-normalization checks cover the stated
families; they are not a full-E decision procedure or arbitrary-recipe privacy
proof.

## Reproduction and residual obligations

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/PairObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3482 jobs), including 21 new public theorem type/axiom
audits and four definition checks. Its 1254 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; another 17 are axiom-free. No
warnings, errors or `sorryAx` occur. The local log is
`tmp/variable-overlap/pair-observation-full-build.log`. The source audit checks
285 public theorem entries and selected stale claims in 17 current-status
documents; it does not replace elaboration or establish log freshness.

Trusted definitions remain E/E0, finite tuples, public recipes, node-count
minimality, general initial frames and fresh nonce allocation. The reality
oracle is the source's initial key/ballot frame and ordered projections in
Appendix B.3, with the repository's documented terminal-tail correction. The
argument uses nonce provenance and suffix length; equal tallies alone do not
identify ballot values. No equation, public operation, custom axiom or
confluence assumption changed.

The subsequent [atomic branch](helios-atomic-observations.md) now derives exact
literal name/constant syntax and evaluation preservation for atomic minima.
Other value heads and transport of arbitrary recipe evaluations must still
establish the global smaller-observation premise. Final partial-decryption
frames and process matching also remain open. The complete objective remains
in the canonical [task list](../../task%20list.md). See the preceding
[partial-decryption branch](helios-partial-decryption-observations.md) and
[static-equivalence interfaces](helios-static-equivalence.md).
