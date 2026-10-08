# Minimum public recipes

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Current status: the [historical origin induction and destructor composition](#minimum-historical-origins-and-destructor-composition)
are machine-checked for all positive candidate counts, both swapped worlds and
arbitrary public-name policies over the initial three-handle frame. This closes
the minimum-recipe structure item. The
[general candidate-substitution development](helios-candidate-substitutions.md)
also checks minimum pair/ciphertext/proof origins, borrowed-aggregate exclusion
and accepted-ballot constructor reconstruction for all valid ground candidates,
including honest abstention and reducible representatives. Source Lemma 9 is
complete with the authorised tail guard; static equivalence and privacy remain
open. Earlier sections record the selected-index and intermediate conditional
interfaces and their controls; validation counts belong to those increments.

`MinimalRecipes.lean` defines `MinimalRecipe restricted σ r`: `r` is public
under `restricted`, and every public recipe `s` with
`EqE (r.subst σ) (s.subst σ)` has at least `r.nodeCount` syntax nodes. The variable
type fixes which handles recipes may use. The substituted values may contain
restricted names; publicness constrains recipe syntax.

This definition makes the recipe policy explicit in Appendix B, Lemma 9's
minimum-size argument. For that lemma, instantiate `restricted` with the honest
nonce set. The separate full-frame policy also forbids the key and auxiliary
names. `nodeCount` counts every constructor and leaf, including constants and
AC operation heads. It is not the E0-invariant termination measure.

## Checked replacement facts

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Every public recipe has a minimum equivalent recipe | Machine-checked | `exists_minimal_recipe` | Fixed substitution, handle type and name policy; substituted E-equality in the conclusion |
| A smaller public equivalent contradicts minimality | Machine-checked | `MinimalRecipe.no_smaller` | Explicit equality and strict size bound |
| Every syntactic subterm of a minimum recipe is minimum | Machine-checked | `MinimalRecipe.subterm` | Every one-hole context; same substitution and policy |
| Minimum recipes are ordinarily irreducible | Machine-checked | `MinimalRecipe.raw_irreducible` | Raw contextual rewriting before substitution |
| Public one-node recipes are minimum | Machine-checked | `MinimalRecipe.of_nodeCount_one` | All terms have at least one node |
| Matching explicit decryption is not minimum | Machine-checked | `MinimalRecipe.not_decrypt_ciphertext` | Ciphertext key E-equals pk of decryption key after substitution |
| Two explicit ciphertexts with matching keys are not minimum as a product | Machine-checked | `MinimalRecipe.not_ciphertext_product` | Key equality after substitution; E7 removes one key recipe |
| Matching explicit partial decryption followed by decryption is not minimum | Machine-checked | `MinimalRecipe.not_partial_decryption` | Key and ciphertext matches after substitution; E6 |

Existence uses the least natural number inhabited by a public equivalent recipe.
It supplies a logical witness, not an executable minimizer or an E-equality
decision procedure. Subterm inheritance uses substitution through contexts,
public replacement and exact preservation of size differences. Raw rewriting
preserves publicness and strictly shrinks `nodeCount`; E7's decrease includes
the positive size of the deleted key. The cancellation lemmas allow matching
that appears only after substitution and expose a smaller public result.

## Controls and limits

`MinimalRecipeSPOT.lean` retains a two-node public-key minimum under identity
substitution. Full-E public-key shape excludes every one-node competitor; this
checks a non-atomic minimum. Its constant subterm instantiates subterm
inheritance. The existential theorem also applies to a reducible public
projection and preserves the actual projected E-value.

The nearby negative controls establish that:

- A restricted literal name is not a minimum public recipe, despite size one.
- A minimum one-node handle can evaluate to an actual projection redex.
- An ordinarily irreducible decrypt can fail minimality because its variable key
  matches after substitution.
- Different key handles with equal values permit E7 to shorten an explicit
  ciphertext product.
- A ciphertext handle can supply E6's matching copy after substitution.
- The raw normal term zero+zero is not minimum: the public constant zero is
  E0-equivalent and smaller.

The last control also preserves the failure of raw-size E0 invariance. These
results do not establish irreducibility modulo E0 of a minimum raw recipe or
normality of its substituted value. In particular, none proves the historical
substitution's exhaustive destructor classification (*) on page 45. That claim
must account for projections of public ballot handles, ciphertext-valued
products and all possible destructor arguments. Binary fst/snd selectors encode
the source's tuple projections; the representation matters for syntax size.
The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

## Reproduce the evidence

Run:

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/MinimalRecipeExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
```

The raw-size refutation gate covers all seven root families, bounded arbitrary
components and every argument position in the fixed signature, with additional
nested wrapping. Seeds 1, 7 and 42 pass, configured for 500 cases and maximum size
40, with `gaveUp=0`; all 256 deterministic inputs pass. The deliberately false
handle-evaluation-normality property fails at n=0, seed 1, zero shrinks. Its
counterexample becomes `minimum_can_evaluate_to_redex`. This gate tests size
mechanics and the stated failure, not the undecided historical classification.

Validation: `lake build` passes (3375 jobs). The public-type and axiom audit
contains 629 nonempty axiom reports, all using only `propext`, `Classical.choice`
and `Quot.sound`, plus 14 axiom-free reports. The final log contains no warnings,
errors or `sorryAx`.

## Indexed tuple selectors and minimum size

`HistoricalSelectorSPOT.lean` checks a representation boundary for the next
classification proof. In the fresh two-candidate frame with names 10, 11,
20–23, the first voter's second ciphertext is
`penc(pk(name 10), name 21, zero)`. The public recipe `fst(snd(var 1))` evaluates
to it and is minimum at three nodes under **every** restricted-name policy.
The recipe itself contains no literal names.

The full-E size lower bound excludes all recipes smaller than three nodes,
including those using arbitrary names. `SmallRecipeBounds.lean` first classifies
all syntax of size at most one or two. Atoms cannot yield the target: the three
handles expose a public key or whole ballots, and names/constants have distinct
normal heads. A unary operator on an atomic name or constant cannot produce a
ciphertext. Immediate unary operations on the three actual handles either
remain incompatible with ciphertext shape, select a different ciphertext nonce,
or select a tuple tail. This exhausts the size-two competitors.

The recipe is exactly `(var 1).project 1`, using the existing zero-based tuple
encoding. It is not `unary f (var v)` for any binary selector `f` and handle `v`.
Its value has the irreducible ciphertext as a reachable descendant. Normalizing
its argument also cannot preserve the outer fst head in that result.
Consequently, a literal single-binary-selector translation of the exception in
Appendix B, page 45 is **refuted**. The paper's actual indexed exception
`π_j(x)` includes this recipe. This is a translation constraint, not a
counterexample to the paper's indexed exception or a new protocol change.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Size-one and size-two syntax are exhausted | Machine-checked | `Term.nodeCount_one_cases`, `Term.nodeCount_two_cases` | All terms, unbounded names and arbitrary variables |
| No ciphertext-valued handle implies size at least two | Machine-checked | `ciphertext_recipe_size_ge_two` | Explicit full-E handle exclusion |
| Also excluding immediate unary handle values implies size at least three | Machine-checked | `ciphertext_recipe_size_ge_three` | Both handle and unary-handle premises required |
| Second historical field requires three nodes | Machine-checked | `second_ciphertext_size_bound`, `second_minimal` | Exact fresh historical frame, all competing names; any public-name policy |
| Outer selector disappears even with normalized arguments | Machine-checked | `second_evaluation_reduces`, `target_irreducible`, `normalized_outer_head_changes` | Reachable normal forms; E0 distinguishes the heads |
| Single-selector exception is too narrow | Refuted | `single_selector_exception_refuted` | Literal binary-selector reading only |
| Indexed source exception covers the witness | Machine-checked | `indexed_projection_exception_applies` | `project 1 = fst ∘ snd`, size three |

The positive control `first_selector_minimal` proves the first ciphertext needs
exactly two nodes and retains its distinct nonce 20. It demonstrates why the
size-three bound needs the unary-handle premise. The separate
`published_ciphertext_minimum` control exposes the target directly and proves a
one-node minimum, demonstrating why the atom-exclusion premise is necessary.
`fresh_accepted_context` connects the main witness to the actual fresh,
empty-board-accepted historical ballot.

The representation gate checks both field outputs with seeds 1, 7 and 42,
configured for 500 cases at size 40 and `gaveUp=0`, plus 256 deterministic
inputs. The false single-selector syntax property fails at n=1, seed 1, zero
shrinks. The output checks use raw evaluation only; the subsequent size and
minimum proofs use full E. Reproduce with `lake build`, the audit command above,
or `lake env lean ExplainableCrypto/Helios/Symbolic/HistoricalSelectorExperiments.lean`.

The later [historical induction](#minimum-historical-origins-and-destructor-composition)
retains indexed field projections and the tuple tails exposed by snd in its
normal-form exception. No general minimum-size formula for every ballot
field or proof projection is claimed by the two-candidate fixture.

Validation of the selector increment: `lake build` passes (3378 jobs). The audit
contains 646 nonempty axiom reports, using only `propext`, `Classical.choice` and
`Quot.sound`, plus 14 axiom-free reports. No warnings, errors or `sorryAx` appear.
All new public theorem statements are printed by `Symbolic/Audit.lean`.

## Decryption with explicit or honest-component ciphertext values

`MinimalDecryption.lean` discharges two decryption cases of the remaining
classification. The substitution and public-name policy stay explicit:

1. The recipe is `dec(a, penc(key, nonce, p))`. Every reachable substituted value
   retains the dec head modulo E0. Every irreducible E-equivalent representative
   has literal dec shape with the same two evaluated argument values. The recipe
   cannot have a ciphertext-valued result, even with reducible target components.
2. The recipe is `dec(a, b)`, and `b` evaluates under full E to a ciphertext whose
   plaintext is a constant. The right-argument recipe may have arbitrary syntax.
   Every irreducible E-equivalent representative retains dec and its two argument
   values. This includes any honest historical ciphertext component.

The proof uses exhaustive [decryption paths](helios-full-structure.md#decryption-paths).
If E5 or E6 ever fires, the returned plaintext is E-equal to the explicit public
subrecipe `p` in the first case, or to the public constant in the second case.
Either replaces the entire decrypt with a strictly smaller public recipe,
contradicting minimum size. The argument covers matching that appears only after
arbitrary reductions, including synchronization of E6's complete ciphertexts.

`decryption_normal_form_of_no_match` also checks the source's composition clause.
Given irreducible representatives of both arguments and the whole decrypt, with
E-equality to their respective source values, the whole representative is
E0-equal to `dec` of the two argument representatives. Contextual irreducibility
and confluence identify the ordered normal components. Normality is a premise;
E-equal but reducible wrappers need not retain a literal dec head.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Explicit ciphertext prevents matching in a minimum decrypt | Machine-checked | `MinimalRecipe.no_explicit_decryption_match` | Arbitrary substitution; plaintext is the explicit public subrecipe |
| Every path retains dec | Machine-checked | `MinimalRecipe.explicit_decryption_path` | Explicit ciphertext argument; actual component paths and E0 endpoint |
| Every normal representative retains dec | Machine-checked | `MinimalRecipe.explicit_decryption_normal_shape` | Irreducible E-equivalent target |
| Independent normal arguments compose to the normal result | Machine-checked | `MinimalRecipe.explicit_decryption_normal_form` | Three normality and value-equality premises |
| No ciphertext-valued output in this minimum case | Machine-checked | `MinimalRecipe.explicit_decryption_not_ciphertext` | Target components need not be normal |
| Constant plaintext permits the same smaller replacement | Machine-checked | `MinimalRecipe.constant_plaintext_no_decryption_match`, `.constant_plaintext_decryption_normal_shape` | Arbitrary right-recipe syntax; explicit ciphertext-value premise |
| Honest component case of (*) | Machine-checked | `Historical.minimum_honest_component_decryption_normal_shape`, `.minimum_honest_component_decryption_normal_form` | Any positive candidate count, both swaps, either voter/component; nonce-only public policy |

The historical theorems use the actual three-handle substitution and require the
right recipe to be E-equal to an honest component in that world. They need no
freshness or secret-key nondeducibility premise: the replacement uses the known
constant plaintext. `historical_projected_decrypt_not_minimal` checks a permitted
literal secret-key name under the nonce-only policy, a projection of an honest
ciphertext, a successful decrypt to one, and failure of minimum size.

A separate sufficient criterion, `MinimalRecipe.of_irreducible_weight`, proves
minimum under identity substitution when a public irreducible term's crypto-weight
equals its raw node count. Every equivalent competitor reaches the term up to E0;
its decreasing crypto-weight is bounded by its syntax size. This criterion proves
a six-node stuck decrypt minimum with distinct variable arguments. Its normal
shape and composition instantiate the new results. It is not a necessary minimum
criterion, nor a claim that crypto-weight always equals syntax size.

The later [historical induction](#minimum-historical-origins-and-destructor-composition)
handles arbitrary minimum right recipes, including products with larger public
plaintexts. The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

Validation of the decryption-path increment: `lake build` passes (3383 jobs).
The audit reports 681 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. The final
log has no warnings, errors or `sorryAx`; every new public theorem type is printed
in `Symbolic/Audit.lean`.

## Public plaintext reconstruction for ciphertext products

`CiphertextProducts.lean` proves the product case of the minimum decryption
argument under an explicit factor-origin certificate. `CiphertextProduct σ key
r p nonce` records a ciphertext recipe `r`, its plaintext recipe `p`, and a
semantic nonce value. Its constructors cover:

- An explicit `penc(k, n, m)` whose key evaluates E-equal to the common key. Its
  plaintext recipe is `m` and its nonce value is the evaluation of `n`.
- Any recipe E-equal after substitution to a constant-plaintext ciphertext,
  provided its syntax has more than one node. Its plaintext recipe is the
  corresponding constant.
- A binary product of two certified recipes under the same semantic key. The
  plaintext recipes combine with add and nonce values combine with compose.

This represents finite nonempty products with arbitrary association and repeated
factors. It introduces no empty-product identity. The nonce field is a semantic
value; a certificate does not supply a public recipe for that nonce.

If the ciphertext recipe is public, its certified plaintext recipe is public
and strictly smaller in raw syntax. Each leaf has that property, and multiplication
and addition add the same one-node overhead. `CiphertextProduct.sound` proves
full-E equality with the ciphertext containing the certified plaintext value,
using E7 at every product node. Thus an E5/E6 match in a minimum decrypt would
return a value with a strictly smaller public recipe. No such match can occur.
The normal-shape and normal-form composition results follow, retaining their
normality and E-value hypotheses.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Certified products have the specified ciphertext value | Machine-checked | `CiphertextProduct.sound` | Supplied certificate and common semantic key |
| Plaintext reconstruction preserves publicness | Machine-checked | `CiphertextProduct.plaintext_public` | Public input ciphertext recipe required |
| Reconstructed plaintext is strictly smaller | Machine-checked | `CiphertextProduct.plaintext_smaller` | Every certificate, including nested/repeated factors |
| Minimum decrypt cannot match a certified product | Machine-checked | `CiphertextProduct.no_minimum_decryption_match` | Minimum under the same substitution and public-name policy |
| Minimum product decryption retains normal shape and composition | Machine-checked | `CiphertextProduct.minimum_decryption_normal_shape`, `.minimum_decryption_normal_form` | Factor certificate, minimum, normality and E-value premises |
| Every historical ciphertext recipe has at least two nodes | Machine-checked | `Historical.frame_ciphertext_recipe_size_bound` | All names and recipes, all positive counts and both swaps |
| Honest component values and actual indexed projections supply leaves | Machine-checked | `Historical.honest_component_product`, `.honest_projection_product` | Actual historical frame; arbitrary component-equivalent recipes or indexed field access |
| Historical product case of (*) | Machine-checked | `Historical.minimum_product_decryption_normal_form` | Explicit certificate; nonce-only policy; all normality and value premises |

The historical size bound first proves that every initial handle exposes a
public key or whole ballot, never a ciphertext. Full-E constructor separation
then excludes every one-node ciphertext recipe, including arbitrary literal
names. This discharges the constant-leaf size premise for honest components.
`Term.subst_drop` and `Term.subst_project` connect the actual indexed recipes to
the existing field-value theorem; both swapped assignments are covered.

Controls assemble a mixed product containing one constructed ciphertext and two
copies of an honest component, with independently specified nonce and message
trees. A swapped-world projection supplies its expected zero plaintext and
nonce 23. A nonce-public decrypt of two copies of the one-valued component
returns one+one and is nonminimum. Full E rejects collapsing that output to one
and rejects certificates that change the public key. A published one-node
ciphertext has no strictly smaller plaintext certificate, demonstrating the
size premise's necessity. The existing six-node stuck minimum instantiates the
normal-form theorem with a constructed leaf.

The gate samples bounded binary product trees with explicit and honest-projection
leaves. Seeds 1, 7 and 42 pass, configured for 500 cases at maximum size 40 with
`gaveUp=0`; all 256 deterministic inputs pass. It checks raw E7 outputs against
separately assembled message/nonce trees and checks the strict syntax-size bound.
The deliberately false duplicate-collapse property fails at n=0, seed 1, zero
shrinks; `duplicate_collapse_rejected` retains its full-E counterexample.
Reproduce with `lake build`, the symbolic audit, or
`lake env lean ExplainableCrypto/Helios/Symbolic/CiphertextProductExperiments.lean`.

The certificate remains a premise. These results do not establish that every
ciphertext-valued recipe in the historical frame has a certified origin, or
that every minimal ciphertext-valued recipe has the source's asserted syntax.
The later [historical induction](#minimum-historical-origins-and-destructor-composition)
derives certificates and constructor/selector/product syntax for every minimum
historical ciphertext recipe. No privacy conclusion follows from plaintext
reconstruction alone.

Validation of the ciphertext-product increment: `lake build` passes (3387 jobs).
The audit reports 706 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. The final
log contains no warnings, errors or `sorryAx`; new public theorem types are
printed by `Symbolic/Audit.lean`.

## Multiplication inversion used by the origin induction

The [full-E multiplication theorem](helios-full-structure.md#full-e-multiplication-inversion-and-output-heads)
now derives ciphertext values for both operands of any ciphertext-valued product,
under the output key. It retains the exact combined nonce and plaintext equations.
The original operands may be projections or other reducible terms, including
factors that expand into products. A normal product result has mul or penc shape;
full E excludes pair, partial-decryption, spk, pk and atomic results.

This supplies semantic premises for recursive analysis of the two operand
recipes. `CiphertextFactors` describes their E-values; `CiphertextProduct` also
records a strictly smaller public plaintext recipe. The later
[historical induction](#minimum-historical-origins-and-destructor-composition)
constructs the latter certificate using minimum subterms and the constructor/
projection cases. Semantic factor values alone do not provide public recipes.

Validation of multiplication inversion: `lake build` passes (3392 jobs).
The audit reports 746 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. New public
theorem types are printed by `Symbolic/Audit.lean`. The final log contains no
warnings, errors or `sorryAx`.

## Arithmetic origins excluded

The [arithmetic output-head results](helios-full-structure.md#addition-and-composition-output-heads)
exclude add and compose as origins of ciphertext, pair, partial-decryption,
proof and public-key E-values. Substitution preserves the arithmetic constructor,
so these exclusions apply directly to instantiated recipes without any minimum
or publicness premise. Add can become zero or one; compose retains its head on
all actual paths. Literal shapes of arbitrary E-equivalent representatives
still require target irreducibility.

This closes the arithmetic exclusions used by the
[historical origin induction](#minimum-historical-origins-and-destructor-composition).
That later theorem derives `CiphertextProduct` for every minimum historical
ciphertext recipe and completes the destructor composition clauses.

Validation of arithmetic output heads: `lake build` passes (3397 jobs).
The audit reports 783 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. New public
theorem types are printed by `Symbolic/Audit.lean`. The final log contains no
warnings, errors or `sorryAx`.

## Minimum proof-checking recipes

`MinimalProofChecking.lean` proves the checking constructor case for arbitrary
substitutions, handle types and public-name policies. If
`checkspk(a,b,c)` is a minimum public recipe, its evaluated value cannot equal
`ok`: the public constant `ok` would be a strictly smaller equivalent recipe.
The [full-E success characterization](helios-full-structure.md#proof-checking-paths-and-full-e-success)
therefore rules out every reachable E8/E9 match, including matches exposed only
after evaluating the arguments.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| A minimum checking recipe cannot succeed | Machine-checked | `MinimalRecipe.check_not_ok` | Full-E inequality to ok; minimum and publicness under the supplied substitution |
| A minimum checking recipe has no reachable E8/E9 match | Machine-checked | `MinimalRecipe.no_proof_check_match` | All three evaluated arguments |
| All paths retain checkspk and component paths | Machine-checked | `MinimalRecipe.proof_check_path` | Arbitrary modulo paths from the evaluated recipe |
| Normal checking results retain component E-values | Machine-checked | `MinimalRecipe.proof_check_normal_shape` | Explicit normal target and evaluated E-value |
| Separately normalized arguments compose modulo E0 | Machine-checked | `MinimalRecipe.proof_check_normal_form` | All four normality premises and all evaluated E-value equations |

The scope covers both historical worlds automatically because it imposes no
special frame condition. It does not claim that substituted minimum recipes
are already irreducible. The four-node control is
`checkspk(var 0,var 1,var 2)` with each handle mapped to
`fst(pair(var i,bottom))`. These reducible values have the same E-values as
identity substitution. The irreducible check on variables has weight and raw
size four, establishing a lower bound on every competitor; substitution
congruence transfers this minimum to the wrapped values. The evaluated check
has actual argument steps and reaches the fixed irreducible check on variables.

The control instantiates normal-form composition and no-match rejection.
Successful delayed checks provide the negative minimum control: each has the
strictly smaller public result ok. A reducible wrapper around the stuck minimum
has the same E-value but lacks checkspk syntax, preserving the normal-target
premise. None of these controls assumes universal substituted normality.

The checking case is complete at this scope. The later
[historical origin induction](#minimum-historical-origins-and-destructor-composition)
also discharges arbitrary minimum decryption and the indexed projection/tail
clauses. The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

Validation of proof-checking paths: `lake build` passes (3402 jobs).
The audit reports 824 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. All new
public theorem types are printed by `Symbolic/Audit.lean`. The final log contains
no warnings, errors or `sorryAx`.

## Projection-chain and tuple-tail origins

`ProjectionChain v r` describes exactly the recipe syntax built from handle v
by applying fst and snd. The predicate adds no operation to the term language.
Every such chain is public under every name policy, since it contains no literal
names. The origin theorems apply to all chain lengths and do not assume minimum
size, normal inputs or ground handle values.

`TupleProjectionChains.lean` assumes that the designated handle is E-equal to a
finite bottom-terminated tuple and that no field has a pair E-value. It proves:

- A pair-valued chain is syntactically `(var v).drop i` with i below the tuple
  length. Thus it consists only of snd operations and denotes a valid tuple tail.
- A ciphertext-valued chain is syntactically `(var v).project i` at a valid field
  index, and that exact field has the supplied ciphertext E-value.
- A proof-valued chain has the analogous indexed form and proof E-value.

The conclusions retain literal recipe equality and index bounds. They do not
merely supply another E-equivalent selector recipe. The tuple and fields may
contain reductions. The non-pair-field premise concerns full E, not literal
syntax: a projected pair has a non-pair literal head but can yield a pair.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Pair/proof-valued projections select from a reachable argument pair | Machine-checked | `EqE.projection_pair_inversion`, `EqE.projection_spk_inversion` | fst/snd only; arbitrary reducible target components |
| Valid tuple tails have actual reduction paths | Machine-checked | `tuple_drop_reduces`, `ReducesModulo.drop` | Index at most length, including the bottom endpoint |
| Pair-valued tuples are nonempty; tuples never have ciphertext/proof values | Machine-checked | `tuple_eqE_pair_nonempty`, `tuple_not_eqE_penc`, `tuple_not_eqE_spk` | Arbitrary field values |
| Indexed selectors and tails are public projection chains | Machine-checked | `ProjectionChain.drop`, `.project`, `.isPublic` | Every index and name policy |
| A non-pair handle cannot reveal pairs through any chain | Machine-checked | `ProjectionChain.not_pair_of_handle` | Explicit full-E non-pair premise |
| A handle with neither pair nor ciphertext value cannot reveal ciphertexts | Machine-checked | `ProjectionChain.not_ciphertext_of_handle` | Both explicit full-E premises |
| Tuple pair/ciphertext/proof chains have exact bounded selector origins | Machine-checked | `ProjectionChain.pair_origin`, `.ciphertext_origin`, `.proof_origin` | Handle tuple E-value and non-pair field premises |
| All historical fields have non-pair values and classified positions | Machine-checked | `Historical.ballot_fields_not_pair`, `.ballot_field_cases` | Ciphertexts, component proofs, aggregate proof; all positive counts |
| Pair-valued historical ballot chains are bounded tails | Machine-checked | `Historical.voter_projection_pair_origin` | Both swapped worlds; no freshness/minimum premise |
| Ciphertext-valued chains select exact honest ciphertext positions | Machine-checked | `Historical.voter_projection_ciphertext_origin`, `.frame_projection_ciphertext_origin` | The latter covers all three handles, retaining voter/index and complete ciphertext E-value |
| Proof-valued ballot chains select a component or aggregate proof | Machine-checked | `Historical.voter_projection_proof_origin` | Exact position alternatives; does not assert unique origin from semantic value alone |
| Public-key handle chains cannot yield ciphertexts | Machine-checked | `Historical.key_projection_chain_not_ciphertext` | Every fst/snd chain |
| Every ciphertext-valued historical chain supplies a product leaf | Machine-checked | `Historical.projection_chain_product` | Explicit chain premise; returns indexed syntax, constant honest plaintext and nonce |

The pair-origin proof inducts over chain syntax. A projection with a pair value
requires its argument to reach a pair. The induction identifies that argument
as a tuple tail. fst would select a field, contradicting the non-pair-field
premise; snd advances the tail index. A pair value prevents advancing to or
past bottom. Ciphertext/proof inversion then forces a final fst at a valid field.
The historical field cases restrict ciphertext positions to the first n+1 fields
and proof positions to the subsequent component and aggregate fields.

The product theorem discharges the certificate obligation for the entire
ciphertext-valued chain class. It identifies the exact honest indexed selector
and invokes its proved product leaf. This is a stronger input to the remaining
induction than a certificate supplied by the caller. It still requires proof
that the recipe is a `ProjectionChain`; it does not assert that every minimum
ciphertext recipe is one.

Controls retain two snd operations reaching an independently written three-proof
tail, including an actual E7 step inside its aggregate field. The checked
three-node minimum second-field recipe instantiates the origin theorem and
certificate construction. Swapping votes preserves its nonce 21 while changing
the selected plaintext from zero to one. Component-proof and aggregate positions
have fixed proof values and cannot yield ciphertexts; a public-key selector chain
also fails. The first out-of-range field is E-equal to fst(bottom), remains
E-distinct from bottom and cannot yield a ciphertext.

The missing-premise controls include the gate's literal pair field and a
syntactically non-pair field that reduces to a pair. In both cases fst can return
a pair, refuting the pure-tail claim when the full-E field restriction is omitted.
The second control has an actual two-step path, not just a failed search.

The gate checks 40 directed/generated selector words per input over tuples with
one to four ciphertext fields followed by the same number of proof fields.
Words include pure tails, valid/invalid indexed fields and selections after a
field; arbitrary field components have bounded generated syntax. Raw normalized
pair/ciphertext outputs are compared with independently assembled word forms
and field values. Seeds 1, 7 and 42 pass (500 configured cases, size 40,
`gaveUp=0`), as do 256 deterministic inputs. The false premise-free pair-origin
claim fails at n=0, seed 1, zero shrinks. This sampled gate does not decide full E;
the general proofs cover the unbounded chain class. Reproduce with `lake build`
or `lake env lean ExplainableCrypto/Helios/Symbolic/ProjectionChainExperiments.lean`.

The later [historical origin induction](#minimum-historical-origins-and-destructor-composition)
connects arbitrary minimum recipes to constructed/chain forms using smaller
subrecipes and the decryption/multiplication results. The chain theorem alone
has the narrower syntax-class scope recorded here. The later [general reconstruction](helios-candidate-substitutions.md) completes
Lemma 9; static equivalence and privacy remain open.

Validation of projection-chain origins: `lake build` passes (3408 jobs).
The audit reports 861 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 17 axiom-free declarations. All new
public theorem types are printed by `Symbolic/Audit.lean`. The final log contains
no warnings, errors or `sorryAx`.

## Minimum historical origins and destructor composition

`HistoricalMinimumOrigins.lean` completes the simultaneous induction over minimum
recipe syntax. A minimum recipe with a pair E-value is either a literal pair
construction or an fst/snd chain rooted at a handle. A minimum ciphertext-valued
recipe has a `CiphertextProduct` certificate under the supplied semantic key,
along with constructor/chain/product syntax. The certificate is proved from
minimum size and the actual historical frame; the caller does not provide it.

The induction keeps the handle type `Fin 3`, the frame parameters and public-name
policy explicit. For projections, the smaller argument's pair origin is either
a literal pair, which contradicts ordinary irreducibility of the minimum whole
recipe, or a chain. The chain classification supplies its exact honest field.
For products, full-E inversion supplies both operand ciphertext values under
the same key; minimum subterms supply their certificates. For decryption, a
reachable E5/E6 match gives the smaller right recipe a ciphertext value. Its
certificate supplies a strictly smaller public plaintext for the whole decrypt,
contradicting minimum size. Constructor separation closes the remaining cases.

`minimum_ciphertext_certificate` returns the actual plaintext recipe p, nonce
value s, certificate, publicness of p, strict raw-size bound, `s =E nonce`, and
`eval(p) =E message` for the caller's ciphertext target. The target key may itself
be reducible: `CiphertextProduct.key_congr` transports certificates along full-E
key equality. The nonce witness is a semantic value, not a public nonce recipe.

Syntax provenance is recorded separately because the generic certificate's
constant-leaf rule alone would not prove a historical origin. The new
`CiphertextRecipeForm n` allows explicit penc constructors, honest ciphertext
selectors at indices in `Fin (n+1)`, and multiplication. Full-E operand inversion
refines every chain leaf to an actual honest position. `minimum_ciphertext_form`
therefore gives a necessary raw syntax form, preserving association and repeated
factors. It does not assert a canonical ordering, an iff for all terms admitted
by the grammar, or an at-most-one-constructed-factor normal presentation.

`HistoricalMinimumProofs.lean` similarly proves that a minimum proof-valued recipe
is an explicit spk or an indexed honest component/aggregate proof selector. This
is constructor provenance; successful proof checking still requires the bit,
key, nonce and complete ciphertext-binding equations from the separate checking
theorem.

| Claim | Evidence class | Declaration | Scope |
| --- | --- | --- | --- |
| Certificates respect semantic key equality | Machine-checked | `CiphertextProduct.key_congr` | Arbitrary substitutions, recipes and reducible keys |
| Pair/proof-valued decryption requires an actual E5/E6 match | Machine-checked | `EqE.decryption_pair_inversion`, `EqE.decryption_spk_inversion` | Arbitrary source/target components |
| Minimum projections cannot select from literal pair recipes | Machine-checked | `MinimalRecipe.projection_chain_of_pair_origin` | Supplied smaller-argument pair origin and explicit fst/snd premise |
| Smaller-right-recipe certificates exclude decryption matching | Machine-checked | `MinimalRecipe.no_decryption_match_of_certificates` | Same substitution and minimum whole recipe |
| Minimum pair origins and ciphertext certificates hold together | Machine-checked | `Historical.minimum_pair_and_ciphertext_origins` | Actual initial historical frame, any name policy, all positive counts and both worlds |
| Minimum ciphertexts have a smaller public plaintext with exact target values | Machine-checked | `Historical.minimum_ciphertext_certificate` | Minimum and ciphertext E-value supplied; no certificate premise |
| Minimum ciphertext syntax has only constructed/honest-selector/product forms | Machine-checked | `Historical.minimum_ciphertext_syntax`, `.minimum_ciphertext_form` | Necessary syntax form under the ciphertext E-value premise |
| Every minimum decrypt has no reachable match | Machine-checked | `Historical.minimum_decryption_no_match` | No assumed ciphertext value or certificate for the right argument |
| Every path from a minimum decrypt retains dec and argument paths | Machine-checked | `Historical.minimum_decryption_path` | Actual modulo paths from the evaluated recipe |
| Minimum decrypts retain normal shape and normal-form composition | Machine-checked | `Historical.minimum_decryption_normal_shape`, `.minimum_decryption_normal_form` | Explicit normality and E-value premises for representatives |
| A pair-producing argument of a minimum projection is a valid honest tail | Machine-checked | `Historical.minimum_projection_argument_tail` | Exact `(var i.succ).drop j` argument syntax, `j < fieldCount n` |
| Minimum projections have the bounded tail exception or compose normal values | Machine-checked | `Historical.minimum_projection_normal_form` | fst/snd only; normal argument/result values supplied independently |
| Minimum proof values have constructed or honest proof origins | Machine-checked | `Historical.minimum_proof_origin`, `.minimum_proof_form` | Explicit spk, component-proof selector or aggregate-proof selector |

The projection theorem states the binary-selector version of source (*). If
its argument can produce a pair, it must literally be a bounded honest ballot
tail. An outer fst is therefore the corresponding indexed field projection;
an outer snd advances that tail. Otherwise the independently supplied normal
argument and result compose modulo E0. The normal-form theorems do not claim
that substituted minimum recipes are already irreducible. The existing minimum
handle with a reducible value and the raw-normal nonminimum controls remain.

The initial historical substitution is load-bearing. These results do not
extend to an arbitrary frame that publishes a ciphertext as a one-node handle.
They do not need name freshness because constructor origins and public plaintext
reconstruction hold even when some historical names coincide. Acceptance/weeding
and the later privacy theorem retain their own assumptions.

### Controls and refutation scope

The three-node minimum second-field selector receives a certificate, public
smaller plaintext, exact nonce 21 and zero message without an assumed origin.
A reducible but E-equal target key exercises certificate transport. A mixed
constructed/repeated-honest product has a minimum representative with certified
plaintext `name 41 + (one + one)` and nonce `name 40 compose (name 20 compose name 20)`.
The plaintext is E-distinct from every constant. The source product itself is
not assumed minimum; minimum existence and the new theorem establish the stated
minimum representative and exact reconstruction. An honest proof also has an
inhabited minimum representative with the proved proof form.

Two controls independently establish minimum sizes in the actual fresh historical
fixture. `dec(name 40,name 41)` is an irreducible three-node minimum: every
size-one/two competitor is excluded, including arbitrary names and unary images
of all three handles. It instantiates the general decryption normal-form theorem.
`fst(name 40)` is an irreducible two-node minimum and forces the retained-selector
branch. The known minimum second ciphertext projection forces the indexed-tail
exception, since its normal ciphertext result cannot have an fst head.

Projected constructed pairs and ciphertexts have the desired E-values but fail
the origin syntax and are nonminimum. A successful known-key decrypt returns the
mixed public plaintext and is nonminimum. A one-node published ciphertext in a
different frame is minimum but has no strictly smaller plaintext certificate.
These controls retain the minimum, frame and normality boundaries.

The executable gate uses a finite catalogue closed under syntactic subterms in
the two-candidate historical fixture. It compares raw-normalized values and
checks every representative with no smaller equivalent in that catalogue.
Pair representatives must be constructed pairs or chains; ciphertexts must pass
the constructed/chain/product condition; proofs must be constructed spks or
chains. The catalogue includes constructed and borrowed values, repeated/mixed
products, projections and known-key decryption wrappers. This is not a global
minimum test or a full-E equality decision procedure.

The final generator varies both selected voter positions and the swap bit
independently, along with three name/proof-position choices: 24 catalogue
configurations. Seeds 1, 7 and 42 pass (500 configured cases, size 40,
`gaveUp=0`), and all 256 deterministic inputs pass. The false pair-origin claim
without minimum size fails at n=0, seed 1, zero shrinks, and has a checked
projected-pair regression. Review of the initial generator found that coupled
selector/swap bits always selected one-valued honest fields; the final generator
removes that coupling and includes zero-valued selections too. The universal
proof covers every positive candidate count and unbounded recipe syntax.

Reproduce with `lake build`, the symbolic audit, or
`lake env lean ExplainableCrypto/Helios/Symbolic/MinimumOriginExperiments.lean`.
The minimum-structure milestone is complete at the scopes above. The later
[general reconstruction](helios-candidate-substitutions.md) applies validity and
weeding to minimum forms for all valid ground candidate substitutions, completing
Lemma 9 with the authorised tail guard. Static equivalence, processes and ballot
secrecy remain open.

Validation of minimum historical origins: `lake build` passes (3416 jobs).
The audit reports 904 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 17 axiom-free declarations. All 43 new
public theorem declarations have type and axiom audit entries; five new origin
and certificate definitions also have type checks. The final log contains no
warnings, errors or `sorryAx`.
