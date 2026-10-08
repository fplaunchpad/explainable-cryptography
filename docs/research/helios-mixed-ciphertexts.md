# Mixed public and honest ciphertext equality

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. For a public encryption multiplied by a nonempty
honest ciphertext combination, equality reduces to the honest occurrence bag
and two smaller public equality observations. This supplies a case for the
remaining static-equivalence argument; all-recipe static equivalence remains
conjectured. The result covers actual `Historical.General.frame` values for
all positive candidate counts, both worlds and arbitrary valid ground candidate
representatives, including abstention and reducible bit terms.

## Separating protected nonce factors

[MixedNonceProvenance.lean](../../ExplainableCrypto/Helios/Symbolic/MixedNonceProvenance.lean)
defines `ProtectedValue restricted r` as the existence of an E-equal value
whose `nonceSafe restricted` check succeeds. The input r may be reducible and
raw-unsafe. `ProtectedValue.normal_rep` obtains an irreducible protected
representative using normalization and forward preservation of protection.

For injectively named honest indices, with every label restricted,
`mixed_named_nonce_eq_iff` proves:

```text
r ◦ nonce(a) =E s ◦ nonce(b)
  iff a.indices = b.indices and r =E s
```

Both r and s must have protected values. After normalization, full-E equality
becomes E0 equality. Filtering the outer composition-factor multiset separates
honest literal names from the remainder factors, preserving multiplicity.
A protected remainder can contain an honest nonce inside an opaque ciphertext
or proof atom. The filter does not inspect such hidden occurrences.

`General.frame_mixed_nonce_eq_iff` discharges protection for arbitrary
nonce-public recipes over the actual frames. It can compare values from
different swap worlds, but its conclusion still requires equality of the
remainder values being compared. It does not assert pointwise equality of
public recipe values across worlds.

## Reducing mixed ciphertext observations

[MixedCiphertexts.lean](../../ExplainableCrypto/Helios/Symbolic/MixedCiphertexts.lean)
defines, with the public-key handle zpk:

```text
mixed(r, p, a) = penc(zpk, r, p) * combinationRecipe(a)
```

`General.mixedCombination_value` gives the fused ciphertext with nonce
`eval(r) ◦ nonce(a)` and payload `eval(p) + message(a)`. Under `Names.Fresh`,
`General.mixedCombination_equality_iff` proves, in either world:

```text
eval(mixed(r, p, a)) =E eval(mixed(s, q, b))
  iff a.indices = b.indices
      and eval(r) =E eval(s)
      and eval(p + zero) =E eval(q + zero)
```

The theorem requires r and s to be public under `Names.nonceNames`. The
logical characterization permits arbitrary p and q. For an application to
public observations, `mixedCombination_public` additionally checks payload
publicness under the caller's policy, including the full restricted-name set.

Equal honest occurrence bags give equal honest message sums within a world.
Every nonempty honest combination has a present numeric sum, possibly zero.
`EqE.add_numeric_value_iff_zero` replaces that common contribution by zero
without changing equality. Numeric presence matters: this does not cancel
zero from arbitrary terms or introduce a general zero identity. See the
[open-variable reflection counterexample](helios-enriched-ciphertexts.md).

`mixedCombination_equality_swap_of_observations` transfers mixed equality
assuming the nonce and zero-padded payload equality observations transfer.
`mixedCombination_subrecipe_bounds` proves that each of these recipes is
strictly smaller than its corresponding mixed recipe. These are explicit
induction interfaces, not an assumption-free proof for arbitrary public recipes.

`mixedCombination_not_public_nonce_constructor` rules out equality between a
mixed value and an encryption with an entirely nonce-public nonce recipe.
A nonempty honest bag supplies a restricted outer nonce factor that such a
recipe cannot deduce. This theorem permits any constructed key and payload,
and does not require a factor-count bound or freshness.

## Claim ledger and independent controls

All declarations below are in `ExplainableCrypto.Helios.Symbolic`;
`General` abbreviates `Historical.General`.

| Claim | Evidence | Declaration | Required scope |
| --- | --- | --- | --- |
| A protected E-value has a protected normal representative | machine-checked | `ProtectedValue.normal_rep` | Existential protection, not raw safety of the original value |
| Honest nonce bags separate from public remainders | machine-checked | `mixed_named_nonce_eq_iff` | Injective restricted labels and two protected remainders |
| Actual frame recipes satisfy the nonce decomposition | machine-checked | `General.frame_mixed_nonce_eq_iff` | Fresh names and nonce-public recipes, arbitrary valid candidates |
| Mixed equality has three exact conditions | machine-checked | `General.mixedCombination_equality_iff` | Same world, nonempty honest trees and nonce-public remainders |
| Two smaller observations suffice for swap transfer | machine-checked | `General.mixedCombination_equality_swap_of_observations`, `General.mixedCombination_subrecipe_bounds` | Transfer of both smaller observations remains a premise |
| A public nonce constructor cannot match a mixed value | machine-checked | `General.mixedCombination_not_public_nonce_constructor` | Nonempty honest product and nonce-public constructed nonce |
| Dropping protection invalidates nonce separation | refuted | `MixedCiphertextSPOT.remainder_protection_required` | Restricted literal remainders compensate for different honest indices |

[MixedCiphertextSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/MixedCiphertextSPOT.lean)
retains ten checked controls. A public selector has a raw-unsafe value with a
protected representative. Its canonical ciphertext payload changes from one
to zero across worlds; `public_remainder_values_differ` rules out pointwise
value preservation as a hidden explanation. A projection wrapper gives an
equal nonce subrecipe within each world.

The positive mixed pair uses these nonce recipes, different trees of the same
four honest occurrences, a repeated factor, and payloads 80 and `80 + zero`.
Both recipes satisfy the full public-name restriction. The first mixed recipe
has exactly 20 nodes and both required observations are strictly smaller.
The negative controls change just the public nonce or add one to the payload.
A separate public constructor has the same raw nonce-factor count as its mixed
target and is still rejected, exercising protection rather than count mismatch.

## Executable gate and validation

`SeparatedNonceExperiments.lean` compares independently generated disjoint
public and honest label lists. Its missing-protection mutation fails at input
n=0, seed 1, with zero shrinks. The corrected cancellation checks pass seeds
1, 7 and 42, each with 500 configured cases, maximum size 40 and `gaveUp=0`,
plus 256 deterministic inputs.

`MixedCiphertextExperiments.lean` evaluates actual general-frame recipes for
one through five candidates, both swaps and abstention/selection pairs. The
nonce recipes include public names, compositions, honest ciphertext selectors
and newly constructed ciphertexts, with projection wrappers or changed factors.
Payloads include a public name and zero, padding, a positive increment, a
changed name and projection. An independently specified index list and two
remainder comparisons predict the observed fused ciphertext equality.

Omitting expected payload padding fails at n=0, seed 1, with zero shrinks.
The corrected gate passes the same three campaigns and 256-input backstop.
The backstop includes all 40 count/candidate-mode/swap configurations, without
claiming exhaustive selected positions or a Cartesian product of recipe forms.
An additional 320 directed inputs, 320 through 639, pass and exercise the
zero-payload and changed-nonce-remainder branches absent from the first backstop.
The observations compare exact lists and numeric summaries for these generated
families; the gate is not a full-E decision procedure for arbitrary recipes.

Reproduce with:

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/SeparatedNonceExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/MixedCiphertextExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3458 jobs), including 25 new public theorem type/axiom
audits and two definition checks. Its 1127 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; another 17 are axiom-free.
There are no warnings, errors or `sorryAx`. The local log is
`tmp/variable-overlap/mixed-ciphertext-full-build.log`. The source audit checks
158 public theorem entries and selected stale claims in 11 current-status
documents; it does not replace elaboration or establish log freshness.

The reality oracle is Cortier–Smyth Appendix B.3 Lemma 10's enriched ciphertext
family, accounting for the checked failure of its open-variable reflection
step. Trusted definitions remain E/E0, nonce protection, public recipes,
nonempty combinations and general candidate validity. No cryptographic
equation, public operation, custom axiom or confluence assumption changed.

## Remaining work

The subsequent [grouping bridge](helios-ciphertext-grouping.md) derives
constructed/honest assemblies from every minimum ciphertext recipe and groups
arbitrary products while preserving semantic key agreement and original-size
bounds. The later [ciphertext induction step](helios-ciphertext-observations.md)
transfers key coherence and all grouped comparisons from a smaller-observation
hypothesis, including the actual minimum-ciphertext branch. A complete argument
must establish that hypothesis globally and handle proof checks and other
destructor contexts. The two smaller observation premises above remain to be discharged
by that argument. Final frames with partial decryptions and historical process
matching also remain open. Keep the full static-equivalence item open in the
[task list](../../task%20list.md).
