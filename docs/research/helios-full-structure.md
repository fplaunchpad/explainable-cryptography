# Full-E constructor structure

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked ordered component equality for ciphertexts, proof
construction, pairing and partial-decryption construction, plus public-key injectivity and exhaustive
projection paths. The inputs may
contain reductions. These lemmas support the ciphertext/proof comparisons in
Cortier–Smyth Appendix B.3, Lemma 9 (pp. 45–46) and Lemma 11 (p. 48).
The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9 with the authorised tail guard. Static equivalence and privacy remain
open. This record preserves the earlier foundation interfaces and their
increment-specific validation counts.

## Checked statements

All declarations are in `ExplainableCrypto.Helios.Symbolic`.

| Claim | Declaration | Scope |
| --- | --- | --- |
| Ciphertext paths preserve all three component paths | `ReducesModulo.penc_components` | Arbitrary modulo paths, including zero steps and E0 endpoints |
| Proof paths preserve four component paths | `ReducesModulo.spk_components` | Arbitrary components |
| Passive binary paths preserve two component paths | `ReducesModulo.passive_binary_components` | Pair or partialDecrypt symbol |
| Full-E ciphertext equality is ordered component equality | `EqE.penc_iff` | Arbitrary inputs; no irreducibility premise |
| Full-E proof equality is ordered component equality | `EqE.spk_iff` | All four fields, including the bound term |
| Full-E passive binary equality compares symbol and components | `EqE.passive_binary_iff`, `EqE.pair_iff`, `EqE.partialDecrypt_iff` | Pair and partialDecrypt only |
| Ciphertexts and proofs are distinct | `penc_not_eqE_spk` | Arbitrary inputs |
| Ciphertexts/proofs differ from passive binary forms | `penc_not_eqE_passive_binary`, `spk_not_eqE_passive_binary` | Explicit passive-symbol premise |
| Full-E name equality is literal name identity | `EqE.name_iff` | Arbitrary name indices |
| An irreducible term equal to a ciphertext/proof has its literal shape | `EqE.penc_irreducible_shape`, `EqE.spk_irreducible_shape` | Target irreducibility is required |

The path proofs induct over `ReducesModulo` and use the exhaustive one-step
constructor cases. Full-E equality supplies a common reduct through the checked
confluence theorem. E0 injectivity at that reduct then compares component paths.
The irreducible-shape corollaries additionally use irreducibility to turn the
target's path into E0 equality. No custom axiom or new symbolic equation is used.

## Controls and validation

`FullStructureExperiments.lean` compares raw normalization of passive constructors
with separately normalized generated components. Seeds 1, 7 and 42 pass,
configured for 500 cases at maximum size 40, with `gaveUp=0`; all 256 deterministic
inputs pass. A false general head-preservation property fails on decryption at
n=0, seed 1, zero shrinks. The gate checks this raw semantics scope, not arbitrary
full-E equality.

`FullStructureSPOT.lean` retains reducible ciphertext/proof fields, a commuted
nonce, multiple component reductions and an E0 endpoint change. Full-E equality
holds where E0 equality fails. A changed message and changed proof binding are
rejected. Pair and partial-decryption arguments cannot be swapped freely.
An irreducible ciphertext instantiates the literal-shape theorem, and a
projection returning that ciphertext refutes dropping irreducibility.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/FullStructureExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
The full build passes (3354 jobs), with 511 axiom reports containing only
`propext`, `Classical.choice` and `Quot.sound`. There are no warnings, errors or
`sorryAx` in the final log.

These are logical observations about terms, not public destructors. They do not
allow a recipe to extract a nonce, key or proof field. Restricted-name
non-deducibility, minimum-recipe origins and
accepted-ballot reconstruction are checked in subsequent developments; see the
[general candidate record](helios-candidate-substitutions.md). Privacy remains
open. Active destructors can
change raw heads under full E, and AC constructors do not have ordered argument
injectivity. Keep those restrictions when using these results.


## Public-key and projection paths

`ProjectionPaths.lean` adds the following machine-checked results.

| Claim | Declaration | Scope |
| --- | --- | --- |
| Public-key paths preserve an argument path | `ReducesModulo.pk_components` | Arbitrary modulo paths |
| E-equal public keys have E-equal arguments | `EqE.pk_iff` | Arbitrary inputs; metatheory, not argument extraction |
| Normal public-key representatives have literal pk shape | `EqE.pk_irreducible_shape` | Irreducible target required |
| Public keys cannot equal ciphertexts | `pk_not_eqE_penc` | Arbitrary inputs |
| Projections retain their head or select from a revealed pair | `ReducesModulo.projection_cases` | fst/snd; actual argument and selected-member paths |
| A ciphertext result forces a pair-producing argument path | `EqE.projection_penc_inversion` | Full-E ciphertext equality; selected member is E-equal to that ciphertext |

Projection inversion does not require a literal pair in the original argument.
It does not establish the source's minimal-recipe classification, which also
uses restricted-name and substitution facts. Both cases in the path theorem can
hold; only exhaustive coverage is claimed.

The gate checks generated raw reductions under pk, nested pair-revealing
projections and stuck names. Seeds 1, 7 and 42 pass (500 configured cases, maximum
size 40, `gaveUp=0`), as do 256 deterministic inputs. The false initial-pair-shape
claim fails at n=0, seed 1, zero shrinks. Checked controls preserve both projection
routes to fixed outputs, the absent initial pair shape, a stuck name projection,
reducible public-key arguments, unequal named keys and an irreducible pk shape.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/ProjectionPathExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3357 jobs pass with 527 axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`. The final log has no warnings, errors or
`sorryAx`. No recipe gains access to a key argument, nonce or proof field.
[Nonce non-deducibility](helios-nonce-nondeducibility.md) and the
[minimum-origin induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
are checked separately. The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

## Minimum-recipe replacement facts

The [minimum-recipe record](helios-minimal-recipes.md) now gives logical existence,
subterm inheritance, ordinary irreducibility and local E5–E7 cancellation under
explicit substitutions and public-name policies. Restricted-name and composed-nonce
non-deducibility are also checked in the [nonce record](helios-nonce-nondeducibility.md).
The later [historical origin induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
classifies minimum pair/ciphertext/proof origins and destructor composition.
A minimum handle can have a reducible value; raw irreducibility is also insufficient
for recipe minimality. Both limits have checked controls.

## Decryption paths

`DecryptionPaths.lean` classifies every modulo path from `dec(a,b)`. Either the
head remains dec with paths from both arguments, or the arguments reach a matching
E5/E6 pattern and the remaining path starts at its plaintext. `DecryptionMatch`
records actual paths from `b` to the ciphertext and from `a` to its key or to the
matching partial decryption. E6 retains the complete repeated ciphertext.
This is a metatheoretic relation over existing operations.

| Claim | Declaration | Scope |
| --- | --- | --- |
| A matching pair of argument paths executes E5/E6 | `DecryptionMatch.reduces` | Exact shared key, nonce and plaintext |
| Every decrypt path retains the head or reaches a matching plaintext | `ReducesModulo.decryption_cases` | Arbitrary contextual/E0 paths, including zero steps |
| Ciphertext result forces a reached match | `EqE.decryption_penc_inversion` | Arbitrary original arguments and target components |
| Reached match from an explicit ciphertext retains its plaintext value | `DecryptionMatch.explicit_plaintext` | Full-E component equality |
| Absence of matching retains normal shape | `decryption_normal_shape_of_no_match` | Explicit no-match and target-irreducibility premises |
| Normal arguments compose to the normal result modulo E0 | `decryption_normal_form_of_no_match` | Explicit no-match, normality and E-value premises |

The path alternatives give exhaustive coverage, not disjointness: a returned
plaintext can itself have a dec head. The ciphertext inversion theorem does not
require initial literal ciphertext syntax. A projection may reveal the ciphertext
after the path starts. The checked negative fixture has exactly that behavior.

`DecryptionPathSPOT.lean` retains delayed E5 and E6 paths through projected keys,
ciphertexts and partial decryptions. Both return a reducible plaintext and then
reach the independently specified ciphertext. A stuck decrypt has no match and
is a six-node minimum under identity substitution. A matching explicit decrypt
reaches a different irreducible head and is nonminimum; an E-equal projection
wrapper around the minimum stuck decrypt shows why target irreducibility matters.
The [minimum-recipe record](helios-minimal-recipes.md#decryption-with-explicit-or-honest-component-ciphertext-values)
derives the explicit-ciphertext and honest-component cases from these paths.

The gate checks delayed E5/E6 outputs with bounded arbitrary components. Seeds
1, 7 and 42 pass (500 configured cases, maximum size 40, `gaveUp=0`), along with
256 deterministic inputs. The false initial-ciphertext-shape property fails at
n=0, seed 1, zero shrinks and has a checked full-E counterexample. The gate uses
raw normalization; the general path proof covers all modulo-E0 paths.
Reproduce with `lake build`, the symbolic audit, or
`lake env lean ExplainableCrypto/Helios/Symbolic/DecryptionPathExperiments.lean`.

Validation of the decryption-path increment: `lake build` passes (3383 jobs).
The audit reports 681 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. The final
log has no warnings, errors or `sorryAx`; every new public theorem type is printed
in `Symbolic/Audit.lean`.

## Full-E multiplication inversion and output heads

`MultiplicationInversion.lean` proves that a product is E-equal to
`penc(K,R,M)` exactly when both operands have ciphertext E-values under K, with
nonce values whose composition is E-equal to R and plaintext values whose sum
is E-equal to M. Inputs, keys, nonces and messages may be reducible. The public
statement requires no literal ciphertext input shape or irreducibility premise.

`CiphertextFactorValues.lean` supplies the underlying factor theorem.
`CiphertextFactors key t` says that every representative of every outer E0
factor of t has a ciphertext E-value under key. Structural folding proves that
this property gives t a ciphertext value. The property is preserved backward
across all modulo steps: a single-factor reduction can be followed backward by
E-equality, including expansion to many factors, while reversing E7 identifies
both input key values from the combined ciphertext. Confluence and passive
ciphertext paths establish the property from any ciphertext E-value of t.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| A term has a ciphertext value exactly when all outer factors do | Machine-checked | `ciphertext_value_iff_factors` | Specified semantic key; all E0 factor representatives |
| Factor values propagate backward through any modulo path | Machine-checked | `ReducesModulo.ciphertext_factors_before` | Exhaustive fusion/factor-step split; expansion allowed |
| Product operands have ciphertext values under the output key | Machine-checked | `CiphertextValue.mul_iff` | Arbitrary terms and key |
| Product equality gives both operand ciphertexts and aggregate equations | Machine-checked | `EqE.mul_penc_inversion`, `.mul_penc_iff` | Exact combined nonce/message E-values |
| A name factor cannot disappear into a ciphertext | Machine-checked | `name_factor_not_ciphertext` | Arbitrary other factor and target components |
| Different key E-values cannot fuse | Machine-checked | `unequal_keys_product_not_ciphertext` | Explicit full-E key disequality |

`MultiplicationHeads.lean` also classifies possible normal product heads.
`ProductEndpoint` means that a term has at least two outer factors or has a
ciphertext E-value. Every product starts with this property. A factor step
preserves a nonempty remainder; an E7 step reaching one factor produces a
ciphertext. Every path therefore preserves `ProductEndpoint`.
`EqE.mul_irreducible_shape` concludes that an irreducible E-equivalent value has
literal mul or penc shape. Target irreducibility is necessary for that literal
shape claim.

Products are full-E distinct from pairing, partial-decryption construction,
proof construction and public-key construction even when those target components
are reducible: `mul_not_eqE_passive_binary`, `mul_not_eqE_spk`, and
`mul_not_eqE_pk`. The atom corollaries also exclude constants, names and variables.
No multiplication identity is added.

Controls expose a projection factor expanding from one to two factors, followed
by a fixed ciphertext result, and instantiate both directions of the product
characterization with independently specified operand values. Different named
keys, an unrelated name factor, passive output heads, duplicate-one collapse and
zero-as-unit are rejected under full E. E0-equivalent keys yield a ciphertext
even when raw normalization leaves the original product unchanged. A reachable
normal value of a product of names inhabits the mul branch; a reducible projection
wrapper demonstrates why literal normal-head classification retains normality.

The gate checks bounded product trees with projected leaves and subproducts,
comparing operand and final raw-normalized values with separately constructed
nonce/message trees. Seeds 1, 7 and 42 pass (500 configured cases, size 40,
`gaveUp=0`), as do 256 deterministic inputs. Cross-key fusion fails at n=0,
seed 1, zero shrinks and has a general full-E rejection theorem. The gate does
not implement full E; the E0-only control explicitly preserves that limit.
Reproduce with `lake build`, the symbolic audit, or
`lake env lean ExplainableCrypto/Helios/Symbolic/MultiplicationInversionExperiments.lean`.

These results supply the multiplication branch's semantic operand inversion.
The `CiphertextProduct` recipe-origin certificate additionally records a smaller
public plaintext recipe. The later [historical induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
derives that certificate for every minimum historical ciphertext recipe.
The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

Validation of multiplication inversion: `lake build` passes (3392 jobs).
The audit reports 746 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. New public
theorem types are printed by `Symbolic/Audit.lean`. The final log contains no
warnings, errors or `sorryAx`.

## Addition and composition output heads

`CompositionHeads.lean` proves that the number of outer composition factors
cannot decrease along any modulo path. A step replaces one factor by a nonempty
bag, including when the factor expands. A composition starts with at least two
factors, so every endpoint retains literal compose shape.

`AdditionHeads.lean` uses `AdditionEndpoint`: an addition summary has a present
numeric component or at least two nonnumeric atoms. A present zero counts as
numeric material. Each addition starts with this property, and E0 equality and
every modulo step preserve it. This restricts endpoints to add, zero or one.
The invariant permits the source's E3/E4 collapses while preventing zero from
disappearing beside an arbitrary name.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Composition factor counts cannot decrease | Machine-checked | `ModuloStep.compose_card_le`, `ReducesModulo.compose_card_le` | All terms and actual modulo paths |
| Composition endpoints retain literal compose shape | Machine-checked | `ReducesModulo.compose_shape` | Arbitrary components, E0 endpoints and factor expansion |
| Addition's numeric-or-multiple-atom invariant persists | Machine-checked | `AdditionEndpoint.add`, `.of_base`, `.step`, `.reduces` | Optional numeric presence distinguishes zero from absence |
| Addition endpoints have add, zero or one shape | Machine-checked | `AdditionEndpoint.shape`, `ReducesModulo.add_shape` | Actual modulo paths |
| Normal E-equivalent representatives have these shapes | Machine-checked | `EqE.compose_irreducible_shape`, `EqE.add_irreducible_shape` | Explicit target irreducibility |
| Arithmetic sources exclude ciphertext and passive outputs | Machine-checked | `arithmetic_not_eqE_penc`, `arithmetic_not_eqE_passive_binary`, `arithmetic_not_eqE_spk`, `arithmetic_not_eqE_pk` | Source symbol add or compose; target components may be reducible |
| Arithmetic sources exclude names and variables | Machine-checked | `arithmetic_not_eqE_name`, `arithmetic_not_eqE_var` | All source components |
| A constant arithmetic value requires addition and zero/one | Machine-checked | `EqE.arithmetic_constant_cases` | Necessary condition; does not assert that arbitrary sums collapse |
| Compose, add and mul are pairwise distinct under E | Machine-checked | `compose_not_eqE_add`, `arithmetic_not_eqE_mul` | All operands, including ciphertext-valued products |

`ArithmeticSeparation.lean` derives the exclusions from confluence and the
preserved endpoint heads. Its generic `arithmetic_not_eqE_of_stable_head`
criterion explicitly requires a target whose head remains stable on all paths
and differs from the source head. The concrete corollaries discharge these
premises. The E0 head tag groups add, zero and one together; literal syntax is
used when distinguishing the numeric collapses from retained add syntax.

Controls retain a composition factor expanding from two outer occurrences to
three, both numeric collapses, and a factor reducing to zero beside a name.
Full-E zero-unit and duplicate-one-collapse claims are rejected. Passive targets
contain reducible components. A projection wrapper around one is E-equal to
zero+one but has neither add nor numeric literal shape and is reducible; this
pins the normal-target premise of the E-equality shape theorem.

The executable gate samples the seven raw rule families, checks composition
counts and addition summaries in arithmetic contexts, and checks the E0
background equation endpoints. Seeds 1, 7 and 42 pass (500 configured cases,
size 40, `gaveUp=0`), along with 256 deterministic inputs. The false assertion
that the zero+zero endpoint retains literal add syntax fails at n=0, seed 1,
zero shrinks. `literal_add_head_can_disappear` retains the actual E-equality
and syntax contradiction as a checked theorem. The sampled gate does not decide
full E; the path theorems supply the universal result. Reproduce with `lake build`
or `lake env lean ExplainableCrypto/Helios/Symbolic/ArithmeticHeadExperiments.lean`.

These arithmetic exclusions are used by the later
[historical origin induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition).
The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

Validation of arithmetic output heads: `lake build` passes (3397 jobs).
The audit reports 783 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. New public
theorem types are printed by `Symbolic/Audit.lean`. The final log contains no
warnings, errors or `sorryAx`.

## Proof-checking paths and full-E success

`ProofCheckPaths.lean` classifies every path from `checkspk(a,b,c)`. The path
either retains checkspk with actual paths from all three original arguments,
or returns exactly `ok`. The successful branch includes `ProofCheckMatch a b c`:
there are a key k, nonce r and bit zero/one such that the three arguments reach
k, `penc(k,r,bit)` and `spk(k,r,bit,penc(k,r,bit))`. This retains the complete
ciphertext binding. Argument matching may appear after reductions or changes
of E0 representative.

Confluence gives two full-E success characterizations. `EqE.check_ok_iff`
equates success with the reachable argument match. The semantic version,
`EqE.check_ok_iff_components`, states:

```text
checkspk(a,b,c) =E ok iff there exist r and bit in {zero,one} such that
  b =E penc(a,r,bit) and c =E spk(a,r,bit,b).
```

The same nonce and bit occur throughout, and the proof's fourth field is the
supplied b. All three input terms may be reducible. The converse proves actual
full-E checking success from these equations.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Reachable argument matches survive earlier component paths | Machine-checked | `ProofCheckMatch.pre` | Same complete E8/E9 instance |
| A reachable argument match returns ok | Machine-checked | `ProofCheckMatch.reduces` | Actual modulo path |
| All checking paths retain components or reach ok | Machine-checked | `ReducesModulo.proof_check_cases`, `.proof_check_shape` | Includes zero steps and E0 endpoints |
| Full-E success is reachable matching | Machine-checked | `EqE.check_ok_iff` | Arbitrary argument terms |
| Full-E success has exactly the specified ciphertext and proof values | Machine-checked | `EqE.check_ok_iff_components` | Common nonce, zero/one guard and supplied ciphertext binding |
| Normal E-representatives retain check components or are ok | Machine-checked | `EqE.proof_check_irreducible_shape` | Explicit target irreducibility |
| No-match checking composes normal values modulo E0 | Machine-checked | `proof_check_normal_shape_of_no_match`, `proof_check_normal_form_of_no_match` | No-match, normality and component E-value premises |
| Checking cannot yield ciphertext or passive constructor values | Machine-checked | `proof_check_not_eqE_penc`, `proof_check_not_eqE_passive_binary`, `proof_check_not_eqE_spk`, `proof_check_not_eqE_pk` | Arbitrary reducible source/target components |
| Checking cannot yield names or variables, and its only constant value is ok | Machine-checked | `proof_check_not_eqE_name`, `proof_check_not_eqE_var`, `EqE.proof_check_constant_cases` | All argument terms |

The head exclusions in `ProofCheckSeparation.lean` use an explicit stable-target
criterion, `proof_check_not_eqE_of_stable_head`. Its concrete corollaries prove
that their target heads remain stable and differ from both checkspk and ok.
`BaseEq.ok_shape` proves that even the E0 endpoint of ok has literal ok syntax.
No new check, projection or cryptographic equation is introduced.

Controls retain delayed success for both bits while the initial raw root matcher
fails, instantiate both semantic-characterization directions, and reject a
changed bound ciphertext and a non-bit vote under full E. The E0-expanded zero
fixture succeeds despite raw matching failure. A reducible projection wrapper
around a stuck check shows why literal E-representative shape requires normality.
The [minimum-checking record](helios-minimal-recipes.md#minimum-proof-checking-recipes)
retains a four-node minimum with reducible handle values and real argument steps.

The gate tests bounded arbitrary keys/nonces, projected checking arguments,
both bits, non-bit and binding-mismatch fixtures, and arbitrary raw-normalized
checkspk/ok outputs. Seeds 1, 7 and 42 pass (500 configured cases, size 40,
`gaveUp=0`), along with 256 deterministic inputs. The false always-retained-head
claim fails at n=0, seed 1, zero shrinks; `literal_check_head_can_disappear`
records an actual path and the literal-syntax contradiction. The gate's raw
normalizer does not decide full E. Reproduce with `lake build` or
`lake env lean ExplainableCrypto/Helios/Symbolic/ProofCheckPathExperiments.lean`.

These results close checkspk behavior for the constructor analysis and expose
the semantic field comparisons needed for accepted-ballot reasoning. The later
[historical induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
completes the minimum-origin and projection/tail clauses. The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

Validation of proof-checking paths: `lake build` passes (3402 jobs).
The audit reports 824 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. All new
public theorem types are printed by `Symbolic/Audit.lean`. The final log contains
no warnings, errors or `sorryAx`.

## Projection inversion and tuple-chain application

`ProjectionInversion.lean` extends the earlier ciphertext-valued projection
inversion to pair and proof values. Every such fst/snd result requires an actual
argument path to a pair and the corresponding selected member E-value. No
literal input shape or target normality premise is imposed. `pk_not_eqE_pair`
separates public-key construction from pair values with reducible components.

`TupleProjectionPaths.lean` proves actual paths to every valid bottom-terminated
tuple suffix, plus full-E tuple/pair/ciphertext/proof exclusions. These support
an exhaustive classification of fst/snd chains rooted at tuple-valued handles
with non-pair fields. The [chain ledger](helios-minimal-recipes.md#projection-chain-and-tuple-tail-origins)
records the raw syntax conclusions, field premises, historical instances and
product-leaf construction. The later [historical induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
uses this chain class to classify arbitrary minimum pair/ciphertext/proof origins.

Validation of projection-chain origins: `lake build` passes (3408 jobs).
The audit reports 861 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 17 axiom-free declarations. All new
public theorem types are printed by `Symbolic/Audit.lean`. The final log contains
no warnings, errors or `sorryAx`.

## Minimum historical origin induction

The [minimum-origin record](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
now discharges the certificate and destructor-composition obligations for every
minimum recipe over the initial historical frame. `MinimumOriginTools.lean`
adds pair-valued decryption inversion, certificate key transport and the explicit
projection/decryption induction steps. `ProjectionNormalForms.lean` composes
normal selector values under a full-E non-pair-argument premise.
`HistoricalMinimumProofs.lean` adds proof-valued decryption inversion and pk/spk
separation, then derives exact minimum proof origins.

The simultaneous pair/ciphertext induction relies on full-E constructor and
product inversion, not merely E0 head tags. The resulting raw ciphertext forms
have constructed ciphertexts, honest ciphertext selectors and multiplication;
proof forms have explicit spks or honest component/aggregate selectors. Target
E-value and minimum premises remain explicit. These facts do not establish
accepted-ballot characterization or privacy.

Validation of minimum historical origins: `lake build` passes (3416 jobs).
The audit reports 904 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 17 axiom-free declarations. All 43 new
public theorem declarations have type and axiom audit entries; five new origin
and certificate definitions also have type checks. The final log contains no
warnings, errors or `sorryAx`.
