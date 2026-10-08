# Multiplication equality through public fusion groups

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. The non-ciphertext multiplication branch for minimum
initial-frame recipes transfers equality in both directions under strictly
smaller public observations. The proof retains ciphertext fusions inside a
product that is not itself a ciphertext. Each final factor has a smaller public
recipe, and their transferred equalities reassemble the original product.

The theorem covers all positive candidate counts and valid ground candidate
substitutions under the full name restriction. It retains both source minima,
supplied multiplication E-values, absence of source ciphertext values, and
`Frame.ObservationsBelow` at the total original recipe size. Supplied components
may reduce. No freshness, destination minimum-size or pointwise factor-value
agreement premise is added. The global smaller-observation premise and
arbitrary-recipe closure remain open.


The [minimum-transport criterion](helios-minimum-transport.md) closes the
generic total-size induction with explicit shared representatives. The
[complete observation assembly](helios-observation-assembly.md) now proves
forward equality preservation for every minimum pair under smaller tests.
Reverse shared minimization supplies destination minima and closes the reverse
step. Initial-frame static equivalence is therefore equivalent to shared
minimization in both directions. Local root minimization with minimum children
is the remaining sufficient proof target in both orientations. A checked
nine-versus-eight-node counterexample still prevents assuming that child
minimization fits the original observation budget.

## Normalize factors before grouping

A plain multiset of full-E leaf classes is insufficient for multiplication.
For example, two equal-key ciphertexts can fuse beside an unrelated public name.
The resulting whole term is still a non-ciphertext product, but its raw outer
factor bag has lost one occurrence through the legitimate E7 fusion. The
unrelated name must remain.

[MinimumMultiplicationOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumMultiplicationOrigins.lean)
proves that a source minimum with an irreducible multiplication value has raw
mul syntax. The destination version uses preserved decryption failure and
reflected pair values under smaller observations. Honest successful selectors
cannot return an irreducible multiplication value. Ciphertext values are
excluded from this normal form by their retained penc head.

`minimum_non_ciphertext_mul_form` accepts arbitrary reducible supplied product
components and an explicit absence of ciphertext values. It normalizes the
supplied product internally and derives the same raw mul origin.

[MultiplicationLeaves.lean](../../ExplainableCrypto/Helios/Symbolic/MultiplicationLeaves.lean)
records raw outer leaves with duplicate occurrences. Every leaf is a minimum
public subterm and lacks raw mul syntax. Its normal representative therefore
has a single outer factor in both worlds. Ciphertext leaves remain permitted.
`minimum_mul_leaf_normal_forms` retains actual modulo paths, irreducibility and
the non-mul normal head, rather than assuming that evaluated leaves are already
normal.

## Normal factor paths consist of fusion

[NormalMultiplicationFactors.lean](../../ExplainableCrypto/Helios/Symbolic/NormalMultiplicationFactors.lean)
defines `BaseClass.Normal` by existence of an irreducible E0 representative.
`Term.NormalMulFactors` requires this property for every raw outer factor.
The whole product can still reduce by fusing ciphertext factors.

`ModuloStep.normal_mul_factors` proves that every step from such a family is
an outer fusion and that the resulting family remains normal. The existing
exhaustive factor-step classification excludes internal rewrites. A fused
ciphertext is normal because its key is normal, its nonce composes normal
inputs, and its message adds normal inputs modulo E0.

`ReducesModulo.normal_mul_factors` lifts this result to actual paths and
produces a ciphertext-fusion path on factor bags. `realize_cipher_fusion_path`
provides the converse realization with an exact final bag. Thus
`eqE_iff_normal_fusion_join` characterizes full-E equality of products of normal
factors by joinability of their bags through ciphertext fusion. It does not
replace fusion joinability with raw bag equality.

## Preserve recipes and the original size budget

[MultiplicationPartitions.lean](../../ExplainableCrypto/Helios/Symbolic/MultiplicationPartitions.lean)
defines `MultiplicationPartition restricted σ source target`. Its pieces pair
public recipes with factor values. The interface records:

| Field | Retained evidence |
|---|---|
| `sourceFactors` | Sum of all piece recipes' E0 factor bags equals the original source bag |
| `targetFactors` | Piece values' E0 classes give exactly the target factor bag |
| `values` | Each piece recipe evaluates to its paired value under σ, modulo E |
| `publicPieces` | Every piece recipe obeys the caller's public-name restriction |
| `budget` | Sum of `(piece recipe node count + 1)` equals `(source node count + 1)` |
| `value` | The original source evaluates to the target modulo E |

The partition tracks occurrences, including duplicate values. An outer fusion
selects exactly two occurrences and replaces their recipes with their product.
It retains the remainder and the exact budget. This budget refers to the
original recipes even when normalizing their values changes raw size.

`MultiplicationPartition.reduces` carries the partition along actual paths from
normal factor families. If at least two final pieces remain,
`piece_smaller` proves that every piece recipe is strictly smaller than the
original source. The other piece has positive size; no empty recipe or public
multiplication unit supplies the bound.

[MinimumMultiplicationPartitions.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumMultiplicationPartitions.lean)
first normalizes raw leaves independently, then carries their partition through
fusion to a fully normal term. `minimum_normal_partitions` derives partitions
in both worlds from source minimum size. For a minimum non-ciphertext product,
value-shape reflection excludes a destination ciphertext value as well. Both
normal forms therefore retain multiplication heads and at least two factors.
`minimum_non_ciphertext_mul_partitions` returns the two normal products,
partitions, and strictly smaller public recipes for every final factor.

## Transfer and reassemble equality

[MultiplicationPartitionTransfer.lean](../../ExplainableCrypto/Helios/Symbolic/MultiplicationPartitionTransfer.lean)
uses exact source factor accounting to reassemble the original recipes under
any destination substitution once their piece-class bags agree. The proof uses
a local full-E multiplication fold with an auxiliary bookkeeping identity; it
adds no object-language unit or equation.

Equal normal endpoints are E0-equal, so their exact target factor bags match.
Each matched pair corresponds to E-equal evaluated piece recipes. A supplied
transfer of these piece equalities gives equal destination piece-class bags
and hence equality of the destination whole recipes.

[MultiplicationObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/MultiplicationObservationInduction.lean)
instantiates this argument as
`Historical.General.minimum_non_ciphertext_multiplication_equality_swap`.
It derives raw mul origins and all four normal partitions. Strict piece-size
bounds put each public comparison below the original total size. Source
partitions prove the forward implication; destination partitions prove the
reverse implication. Neither direction assumes destination minimum size.

This closes the non-ciphertext multiplication branch under the explicit bounded
premise. It does not prove that premise, transport arbitrary nonminimum
source evaluations, or establish full static equivalence.

## Controls and verification

[MultiplicationObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/MultiplicationObservationSPOT.lean)
contains twelve public controls. A same-key fusion beside a name retains
normal factors, full-E equality and a non-ciphertext whole value while changing
the raw bag cardinality. Its normal endpoint instantiates fusion joinability.
A concrete public partition has exactly two final pieces and strict recipe
budgets after fusion. Wrong keys cannot yield any ciphertext. Hidden products
refute omission of normalization, repeated factors stay observable, the
unrelated remainder cannot disappear, and zero is not a multiplication unit.

Literal name products attain exact three-node minima for all valid candidate
assignments and both swaps. Distinct permuted minima instantiate the complete
branch with a reducible supplied target; unequal multiplicities instantiate
its negative companion. Their six-node bounded premises use diagonal candidate
assignments. A public nonminimum wrapper retains the minimum-origin boundary.
The generic fusion control exercises grouping directly; the complete-branch
controls do not claim a different-vote privacy proof from finite examples.

`MultiplicationObservationExperiments.lean` first detects the unfused-bag and
hidden-product defects at input 0, seed 1, zero shrinks. The positive partition
gate passes seeds 1, 7 and 42 with 500 configured cases, size 40 and `gaveUp=0`,
plus 2048 deterministic inputs. It partitions two through eight ciphertext
occurrences by literal keys, with repeated nonces and both bits, and retains
an unrelated name. Independent occurrence counts and raw recipe sizes check
the partition budget. A separate literal E7 fixture checks the exact combined
nonce/message and the retained outer factor count. These executable proxies
are not full-E equality procedures; general statements have kernel proofs.

```sh
lake build
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/multiplication-observation-full-build.log
```

The full build passes 3525 jobs, including 39 new public theorem type/axiom
audits and thirteen definition/field checks. It reports 1433 nonempty axiom
sets using only `propext`, `Classical.choice` and `Quot.sound`, plus 17 axiom-free
reports. No warnings, errors or `sorryAx` occur. The source checker covers
464 public theorem audit entries and 25 current-status documents; it does not
replace elaboration or establish build-log freshness.

Trusted definitions remain E/E0, actual modulo paths, minimum public recipes,
raw node counts and the general initial frames. The reality oracle is source
E7 under AC multiplication, including equal-key fusion of nonadjacent factors
with an unrelated remainder. No equation, public operation, custom axiom or
assumed confluence changed.

The global smaller-observation premise, arbitrary nonminimum evaluation
transport and full arbitrary-recipe closure remain open. Final frames
publishing partial decryptions and historical process matching remain required.
See the preceding [addition record](helios-addition-observations.md),
[static-equivalence interfaces](helios-static-equivalence.md) and canonical
[task list](../../task%20list.md).
