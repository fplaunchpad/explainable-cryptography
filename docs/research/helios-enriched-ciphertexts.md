# Enriched ciphertext equality and numeric presence

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: the encoded instance of the E0 reflection step in Cortier–Smyth
Appendix B.3, Lemma 10 Claim 2 is refuted. The counterexample is machine-checked
and arises from permitted ciphertext-combination recipes with fresh names.
It does not distinguish the two vote worlds and does not refute Lemma 10 itself.
The corrected numeric-offset results and honest-product equality results below
are machine-checked; general static equivalence remains open.

## Why equality does not reflect to open vote variables

Let `v` be the first honest voter's open vote variable, `P` a public name, `s` a
fresh public nonce and `r` an honest restricted nonce. Consider the fused values:

```text
L = penc(pk(k), s ◦ r, P + v)
R = penc(pk(k), s ◦ r, (P + zero) + v)
```

Before candidate substitution, the plaintext's E0 summary has no numeric
summand on the left and a present zero on the right. E0 does not give zero a
general identity law, so these are distinct E0 classes. After substituting
zero or one for `v`, both plaintexts have the same atom bag and numeric count.
Thus `Lτ =E0 Rτ` holds for both substitutions, although `L ≠E0 R`.

[NumericReflectionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/NumericReflectionSPOT.lean)
checks this with key name 10, public nonce 40, honest nonce 20 and public payload
name 41. `open_ciphertexts_not_baseEq` uses passive-constructor inversion and
exact optional numeric summaries to prove the distinction.
`substituted_ciphertexts_baseEq` checks both assignments. The formal
`open_equality_reflection_false` packages the failed reflection property.

The values correspond to the permitted recipes
`penc(zpk, 40, 41) * π1(y1)` and
`penc(zpk, 40, 41 + zero) * π1(y1)`. The fixture has two honest voters, one
candidate, honest abstention and a selected vote; all key, auxiliary and honest
nonce names are fresh. `public_product_recipes` checks full-policy publicness,
and `public_products_equal_both_worlds` derives their actual general-frame
values using E7. Both recipes are equal in both worlds. The failure concerns
reflection to the open enriched frame, not vote privacy.

This case belongs to the paper's enriched ciphertext family: the public nonce
and protected nonce multiplicities are the same, while the public payloads are
`P` and `P + zero`. Randomness alone therefore cannot justify the stated step
back to equality of open payload expressions. The source correspondence is a
comparison with that family and Claim 2; an infinite extended-frame datatype
has not been implemented here.

## Correct cancellation after a numeric contribution

[NumericOffsetEquality.lean](../../ExplainableCrypto/Helios/Symbolic/NumericOffsetEquality.lean)
proves the exact condition. For addition summaries `a`, `b` and any natural
number `k`, adding the common numeric summary `number k` gives equality exactly
when:

```text
a.atoms = b.atoms
and a.numeric.getD 0 = b.numeric.getD 0
```

Once a numeric contribution is present, absent numeric content and present
zero are indistinguishable in the remaining payload. The value `k` cancels;
its presence cannot be discarded. Consequently, equality after adding `k` is
equivalent to equality after adding any other common natural count `l`.

`BaseEq.add_numeric_offset_iff` transfers this fact to exact E0 term equality.
`EqE.add_numeric_offset_iff` handles arbitrary reducible payloads under full E:
it obtains normal representatives internally, uses confluence to pass to E0,
then returns to the original values. The ciphertext versions retain a common
key and nonce and use constructor injectivity. No caller normality premise,
general zero identity, composition unit or multiplication unit is introduced.

`positive_increment_not_erased` proves that adding one instead of zero remains
distinct. `reducible_payload_offset` checks a projection payload against a
different zero-padded representative for every common numeric count. These
controls exclude a constant equality test or accidental loss of all numeric
information.

## Nonempty honest ciphertext combinations

[CiphertextCombinations.lean](../../ExplainableCrypto/Helios/Symbolic/CiphertextCombinations.lean)
defines `Combination α` with a leaf and a binary combination constructor.
There is no empty case. `Combination.indices` retains the multiset of leaf
occurrences, and `evaluate` interprets the tree under an operation and leaf
values. A local commutative-semigroup construction proves rearrangement under
any of the existing AC operations. Its adjoined algebraic unit is bookkeeping;
the datatype inserts no unit term or new E0 equation, and the exported quotient
multiplication instance is unchanged.

For `Historical.General.HonestIndex n = Fin 2 × Fin (n + 1)`, the public recipe
selects the indicated honest ciphertext fields and multiplies them according
to the tree. The value theorem gives one encryption under the public key with
the exact composed nonce tree and plaintext addition tree. It covers arbitrary
valid ground candidate substitutions and every positive candidate count.

Fresh nonce labels determine the entire occurrence multiset from full-E nonce
equality. The proof first establishes irreducibility of the named composition,
then uses confluence, composition-factor equality and injectivity of the name
assignment. Equality of the ciphertext recipe values is therefore exactly
equality of the index multisets. This proves an unbounded equality-test
invariance result for the honest-product grammar in both worlds, including
reassociation, permutation and repeated factors.

`Combination.evaluate_bit_sum` and `General.combinationMessage_numeric` show
that each nonempty honest combination has a present natural-number plaintext
sum, including zero for an all-abstention combination. The count may change
when votes swap. `General.combination_offset_equality_swap` nevertheless proves
that comparing two fixed payloads after adding this common honest sum gives
the same equality result in both worlds. It follows from the corrected full-E
numeric-offset theorem, not from equality of the hidden sums.

## Claim ledger

All names below are in `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Open-variable E0 reflection fails | refuted | `NumericReflectionSPOT.open_equality_reflection_false` | Explicit fused ciphertext pair, equal after both bit substitutions and E0-distinct before |
| Counterexample comes from public source-frame recipes | machine-checked | `NumericReflectionSPOT.public_products_equal_both_worlds` | Fresh one-candidate frame; equality in both worlds |
| Numeric presence determines the corrected cancellation rule | machine-checked | `AddSummary.combine_number_eq_iff` | All summaries, exact atom multiplicity and numeric value |
| A common numeric offset can change without changing equality | machine-checked | `BaseEq.add_numeric_offset_iff`, `EqE.add_numeric_offset_iff` | Arbitrary payload terms; full-E version permits reducible payloads |
| Ciphertext version of offset invariance | machine-checked | `EqE.ciphertext_numeric_offset_iff` | Common fixed key, nonce and two payloads |
| Equal occurrence bags permit AC rearrangement | machine-checked | `Combination.evaluate_baseEq_of_indices` | Arbitrary nonempty combination trees and term values |
| Fresh nonce equality recovers exact occurrences | machine-checked | `Combination.named_nonce_eq_iff` | Injective name assignment; full E; repeated labels retained |
| Honest product recipe has its precise homomorphic value | machine-checked | `General.combination_value` | Actual general frame, both worlds, every positive count |
| Honest product equality is exactly index-bag equality | machine-checked | `General.combination_equality_iff_indices` | `Names.Fresh`; honest-selector product grammar |
| That equality test is invariant under vote swap | machine-checked | `General.combination_equality_swap` | All nonempty trees in this grammar, not all public recipes |
| Honest combination has a present numeric plaintext sum | machine-checked | `General.combinationMessage_numeric` | All valid ground candidates, including reducible bit representatives |
| Fixed-payload comparison survives a changed honest sum | machine-checked | `General.combination_offset_equality_swap` | Same nonempty honest combination and same two payload values |

`CiphertextCombinationSPOT.lean` checks a four-leaf product with a repeated
nonce, a different tree/order of the same factors, and a three-leaf product
with one occurrence removed. Rearrangement preserves equality; removing the
occurrence does not. The same finite set of indices cannot replace the multiset.
A nonce collision separately defeats provenance. Another control changes the
hidden plaintext sum from two to zero across worlds while retaining the fixed-
payload equality equivalence; no tally-equality premise supports the result.

## Executable scope

`NumericReflectionExperiments.lean` first rejects the naive reflection property
at generated index n=0, seed 1, zero shrinks. The positive gate uses exact
`AddSummary Nat` values with optional numeric content and atom bags. It checks
the corrected equality criterion, independence from the common numeric offset,
zero-padding absorption and nonzero-increment rejection. These are summary-
algebra tests; the generator may include the empty bookkeeping summary and
does not assert that every generated summary is a represented term.

`CiphertextCombinationExperiments.lean` evaluates actual general-frame public
recipes at counts one through five, both swaps and valid abstention/selection
pairs. It compares exact nonce occurrence lists and numeric plaintext summaries
with independently specified field indices and expected one counts. Each input
checks two rearranged four-leaf products and a product with the repeated leaf
removed. The 256-input backstop includes all 40 count/pair-mode/swap configurations;
selected positions vary without claiming their full Cartesian product. The
multiplicity and nonce-injectivity negative controls each fail at generated
index n=0, seed 1, zero shrinks.

Both positive suites pass seeds 1, 7 and 42, with 500 configured cases per seed,
maximum size 40 and `gaveUp=0`, plus all 256 deterministic inputs. The product
gate observes raw E7 fusion and exact named-factor/numeric summaries. It does
not decide full E on arbitrary recipes. The initial algebra-only product gate
also passed; the retained gate strengthens it to actual valid candidate frames.

## Remaining static-equivalence work

The subsequent [mixed-ciphertext reduction](helios-mixed-ciphertexts.md) handles
a public encryption multiplied by a nonempty honest product, with arbitrary
public nonce and payload subrecipes. It reduces equality to an honest occurrence
bag and two strictly smaller observations. Their transfer is still an explicit
premise. Arbitrary products, proof checks and destructor contexts remain part
of the full closure and observation argument. The fixed-payload offset theorem
in this record does not itself justify world-dependent public recipe values. Final partial-decryption frames, complete
tally/process matching and protocol privacy remain open. Use the
[static-equivalence record](helios-static-equivalence.md) and the canonical
[task list](../../task%20list.md) when continuing.

## Reproduce the evidence

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/NumericReflectionExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/CiphertextCombinationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3453 jobs), including 33 new public theorem type/axiom
audits and ten new definition/type checks. All 1102 nonempty axiom reports use
only `propext`, `Classical.choice` and `Quot.sound`; another 17 reports are
axiom-free. The completed build contains no warnings, errors or `sorryAx`.
The local log is `tmp/variable-overlap/enriched-ciphertext-full-build.log`.

Trusted semantics remain the existing E/E0 equations, exact optional numeric
summaries, public recipes, general candidate frames and fresh nonce assignments.
The independent source is Cortier–Smyth Appendix B.3 Lemma 10 and its enriched
ciphertext family. No cryptographic equation, public operation, custom axiom or
confluence assumption was introduced. The result changes the proof strategy,
not the protocol model or the privacy objective.
