# Confluence modulo the background equations

Status: confluence modulo E0 is machine-checked for every term in the encoded
rewrite system. `GlobalConfluence.lean` discharges all component and factor-local
premises by simultaneous structural induction. Together with checked termination,
this proves unique irreducible descendants modulo E0 and characterizes full E
equality by joinability. See [global confluence](#global-confluence) for the
public statements, controls and validation.

The sections below preserve the development sequence. Their earlier statements
that local confluence, singleton sources or component/factor premises remained
open describe those increments; the global proof discharges those obligations.
The foundational conditional lemmas keep their explicit parameters, and the
new unconditional theorems supply them. Full-E structural analysis and privacy
remain separate obligations.

Goal: justify the use of unique normal forms modulo E0 in the historical
accepted-ballot and static-equivalence arguments. The candidate claim is that
any two reductions from the same term have descendants equal modulo E0.
Raw syntactic equality of endpoints is a deliberately false alternative:
a projection can return zero or an E0-equivalent `zero + zero`, both irreducible
under the oriented rules and syntactically distinct.

The proof separates a generic termination-plus-local-confluence argument from
protocol-specific overlap proofs. The final simultaneous induction supplies
the local-confluence premise; the generic implication alone does not.

The first directed source overlap has three ciphertexts under the same key.
Combining the first two then the third yields left-associated nonce/plaintext
combinations. Combining the last two first yields right-associated ones. AC in
E0 joins the results. The independent oracle is E7 with associativity of `*`,
`+` and nonce composition in §5.2.1 and Appendix B.2.2. No identity law is used.

Before proving that overlap for arbitrary terms, test the two routes with the
existing certified root matcher and an explicit one-associativity alignment of
the expected endpoints. Keep the false raw-equality test and all mismatch/failure
outcomes visible. This is a directed family, not enumeration of all critical
pairs or proof of their completeness.

The initial obligations were fixed-constructor overlaps involving nonlinear
proof/decryption rules, background-equation interactions and exhaustive coverage
of arbitrary competing reductions. The subsequent analyses and global induction
now discharge these without introducing local confluence as an axiom.

## Checked results and exact scope

All declarations are in `ExplainableCrypto.Helios.Symbolic`.

| Claim | Evidence | Remaining hypothesis or limit |
| --- | --- | --- |
| Reductions can be transported through all contexts and E0 representatives | `ModuloStep.context`, `ReducesModulo.context`, `ModuloStep.pre_base`, `ModuloStep.post_base` | Properties of the defined relations |
| Termination and local confluence imply confluence modulo E0 | `confluence_of_local_confluence` | Explicit `LocalConfluentModulo V` parameter, now supplied by `local_confluence_modulo` |
| Irreducible descendants are unique modulo E0 | `normal_forms_unique_of_local_confluence` | Same explicit hypothesis |
| E-equality is equivalent to joinability | `eqE_iff_join_of_local_confluence` | Same explicit hypothesis; E itself is unchanged |
| E-equality of irreducible terms reduces to E0-equality | `irreducible_eqE_iff_base_of_local_confluence` | Local confluence and irreducibility are explicit hypotheses |
| The homomorphic three-ciphertext peak is reachable and joinable | `triple_peak_joined` | Unconditional, for arbitrary terms under one shared encryption key |
| Raw syntactic confluence is false for the modulo-step presentation | `raw_confluence_false` | Irreducible endpoints zero and zero+zero remain E0-equal |
| Root and variable-position reductions join | `variable_peak_joined` | Explicit schema context and competing step inside its substituted variable |
| E0 preserves rigid constructor shape and arguments | `BaseEq.argument`, `BaseEq.penc_shape`, constructor `*_iff` lemmas | E0 only; binary inversion excludes AC operators |
| Two ciphertext factors match directly or swapped | `ciphertext_product_pairing` | E0-equal products of exactly two ciphertext factors |
| Every pair of E0-aligned root-rule instances joins | `root_outputs_base`, `root_peak_joined` | Root instances; differing contextual redex placements remain unclassified |
| Ordinary contextual rewriting is confluent | `ordinary_rewriting_confluent`, `raw_contextual_peak_joined` | `RawReduces`/`RewriteStep`, without background steps |
| Raw normalization cannot solve modulo-E0 confluence | `RawNormalizationSPOT.raw_normalization_incomplete_modulo` | A raw-irreducible source has a modulo step with non-E0-equal normalized endpoints |
| The quotient factor multiset determines E0 equality | `baseEq_iff_mulFactors` | Exact quotient classes, not the factor-tag approximation |
| Any specified ciphertext pair can be selected | `homomorphic_selection_reachable` | Input factor decomposition; output step and exact residual factors |
| Specified shared/disjoint selections join with arbitrary remainders | `shared_homomorphic_selections_joined`, `disjoint_homomorphic_selections_joined` | Branch factor decompositions are explicit; arbitrary-pair case classification remains open |

`ReducesModulo` includes a final E0 equality even for zero oriented steps.
This permits two terminal representatives of the same background class to be
joined. The earlier `Reduces` relation is retained and embedded explicitly;
its zero-step case is literal identity. `JoinModulo.sound` connects joins back
to the original E-equality.

The three-ciphertext theorem proves actual reductions from a common ancestor
to both intermediate branches, then reductions to E0-equivalent endpoints.
It does not merely prove the two expressions equal in E. It covers one
homomorphic overlap family, not the completeness of a critical-pair analysis.

## Refutation gate

`ConfluenceExperiments.lean` runs the two combination orders through the certified
root matcher. A deliberately false equality of raw endpoints fails with seed 1,
`n=0`, zero shrinks; `triple_raw_endpoints_differ` retains that mismatch. The
stronger `raw_confluence_false` control proves why syntactic joining is the wrong
objective, rather than merely recording unequal intermediate expressions.

The positive campaign checks both successful reduction routes and their endpoint
alignment for seeds 1, 7 and 42, each configured for 500 instances and maximum
size 40. All three succeed with `gaveUp=0`. Inputs use the existing depth-0–3
term generator; no premises are filtered. The alignment function handles only
the known associativity pattern. It is not a background normaliser. The
parametric theorem `triple_endpoints_base` independently checks the necessary
E0 equivalence for arbitrary arguments.

The campaign ran before the parametric overlap proof. These results support
only that directed family. Variable overlaps are now covered below.
Fixed-constructor overlaps and exhaustive case coverage remain open in the
canonical task list.

## Reproduction

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/ConfluenceExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
```

The audit checks all new public theorem types and prints their axioms. Conditional
results retain their hypotheses in these types; no local-confluence or privacy
axiom was added to make them unconditional.

Original confluence increment validation: `lake build` passes (3287 jobs). The audit reports only
subsets of `propext`, `Classical.choice` and `Quot.sound`, with no custom axioms
or `sorryAx`. No build warnings or errors were reported.

## Variable-overlap investigation

Claim: a root-rule instance and a competing reduction inside one occurrence of
one substituted variable join modulo E0 by performing the same reduction in
its remaining occurrences. This includes repeated key, nonce and plaintext
parameters in nonlinear rules, provided the competing reduction
lies inside a schema variable. It does not cover overlaps at fixed constructor
positions or prove that arbitrary E0 representatives have this form.

Status: machine-checked.
Formal oracle: `variable_peak_joined` in `VariableOverlap.lean`, with an explicit
schema context, root rule, substitution and competing `ModuloStep` premise.
Falsifier: a repeated-variable instance whose branches cannot reach the common
substituted right side after synchronising their remaining copies.
Positive control: projection in a decryption key; both key copies reduce to the
same name and decryption returns the independently chosen plaintext.
Negative control: reducing only the outside key prevents raw root matching;
a matcher that always returns the plaintext must fail this control.
PBT gate: directed projection substitutions in all seven root-rule schemata;
seeds 1, 7 and 42, each configured for 500 instances and maximum size 40.
All three runs succeed with `gaveUp=0`. A deterministic backstop passes for
inputs 0–255. The negative control fails at `n=0`, seed 1, zero shrinks.
Trusted definitions: `RootStep`, `Context.fill`, `Term.subst`, `ModuloStep`,
`ReducesModulo` and `JoinModulo`.
Reality oracle: E1, E2 and E5–E9 in Cortier–Smyth §5.2.1 and Appendix B.2.2;
copy synchronisation is a rewriting argument about these exact schemata.
Residual assumptions and unsupported cases: fixed-constructor overlaps,
E0 rearrangement coverage, and full local confluence remain open.

The public theorem takes `RootStep (c.fill (.var v)) r`, a substitution `σ`,
and `ModuloStep (σ v) b`. It returns both reductions from the shared source
and `JoinModulo (r.subst σ) ((c.subst σ).fill b)`. The proof updates only `v`
in `σ` to `b`, reduces all its remaining occurrences in the schema context,
and applies the substituted root rule. The root branch reduces its residual
copies to the same substituted right side. The proof works for arbitrary
variable types and arbitrary terms; it requires no `LocalConfluentModulo`
hypothesis. `ReductionSubstitution.lean` supplies the congruence and context
substitution lemmas.

`VariableOverlapSPOT` retains concrete peaks for decryption, partial decryption,
and both proof checks. `one_copy_changed_no_root_match` retains the negative
control; `remaining_copy_reduces` independently gives the missing context step
and final decryption to one. Thus the failed raw match is not mistaken for
irreducibility. These fixtures follow E1, E5, E6, E8 and E9 directly.

The campaign in `VariableOverlapExperiments.lean` checks projection of a key
parameter, raw matching before and after synchronisation in all seven rule
fixtures, and interrupted decryption matching. The other parameters use the
existing depth-0–3 generator. This is a directed executable approximation of the
variable-overlap claim, not enumeration of every occurrence or reduction.
The general theorem supplies that broader variable-overlap evidence.

Reproduce with `lake build`, then
`lake env lean ExplainableCrypto/Helios/Symbolic/VariableOverlapExperiments.lean`
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Variable-overlap increment validation: `lake build` passes (3290 jobs), including the new declarations,
controls and campaigns. The public-type and axiom audit reports only subsets
of `propext`, `Classical.choice` and `Quot.sound`; the substituted root rule
uses no axioms. The final build reports no warnings or errors.


## Rigid constructors and root overlaps

Status: machine-checked; the combined structure/root increment passes
`lake build` (3295 jobs), including controls and the public-type/axiom audit.

`BaseStructure.lean` proves that E0 preserves rigid constructor tags and fixed
argument positions. `BaseEq.penc_iff` extracts E0 equality of ciphertext keys,
nonces and plaintexts; `BaseEq.penc_shape` also reconstructs the shape of an
arbitrary E0-equivalent representative. The corresponding unary, rigid binary,
ternary and proof lemmas retain symbol equality as well as argument equality.
The binary lemma explicitly requires `¬ AC` for both operators.

`HeadTag` groups zero, one and addition together because E3/E4 change their
raw outer constructors. It is an invariant, not a complete equality test.
`rigidArgument` leaves AC argument positions opaque. Both functions operate
at the metatheory level and are absent from the public recipe signature.
The positive nonce-commutation fixture and the negative multiplication fixture
show why rigid constructor inversion cannot be applied indiscriminately.

`rigid_root_outputs_base` proves that any two root-rule instances with
E0-equivalent left sides have E0-equivalent right sides, provided the first
root is not homomorphic multiplication. `rigid_root_peak_joined` returns both
steps from the same source and a join. The proof checks all rule pairs:
projections return a fixed path through a pair; both decryptions return the
plaintext path through their ciphertext; proof checks return `ok`. Distinct
rigid head symbols cannot be E0-equal. No local-confluence hypothesis appears.

`decrypt_partial_sources_not_base` rules out an E5/E6 source overlap. Equating
the ciphertexts equates their keys; equating the decryption arguments would
then equate a key with a partial-decryption term containing an equivalent key.
This contradicts the checked E0-invariant weight.

The independent controls include `RigidRootSPOT.projection_outputs_not_identical`:
the projection outputs zero and zero+zero are joined modulo E0 but differ as
syntax. `decrypt_commuted_nonce` joins the decryption routes for a nonce and
its commuted composition. These retain actual rule instances and their
source E0 equality, rather than only checking equal outputs.

The observation gate ran before the general structure proofs. It tests all
eight E0 generating fixtures, generated contexts and nonconstant rigid-tag
fixtures. Seeds 1, 7 and 42, each configured for 500 instances at maximum size
40, pass with `gaveUp=0`; deterministic inputs 0–255 also pass. The deliberately
wrong raw-constructor invariant fails at `n=0`, seed 1, zero shrinks.
`BaseStructureSPOT.addition_can_change_root` retains the source counterexample.
This campaign tests observations and does not enumerate all competing steps.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/BaseStructureExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.

Homomorphic root matching is now covered below. Remaining obligations include
structural nesting of competing redexes, disjoint contexts, AC redex placement
in larger products, and a theorem reducing every pair of modulo steps to the
checked cases. The E0 constructor
lemmas alone do not prove constructor properties for full E, nonce
non-deducibility, accepted-ballot characterisation, or ballot secrecy.


## Homomorphic factors and complete root overlap coverage

Status: machine-checked. This section covers root-rule instances with
E0-equivalent sources, not arbitrary pairs of contextual reductions.

`baseSetoid` uses the existing `BaseEq` relation and its checked equivalence
properties. `baseClass_eq_iff` shows that quotient equality is exactly E0
equality. `Term.mulFactors` flattens only top-level multiplication into a
multiset of these classes; all other terms remain single factors.
`BaseEq.mul_factors` proves invariance under arbitrary E0 equality, including
equations inside factors. The construction is metatheory, not a normaliser or
an added public-recipe operation.

`ciphertext_product_pairing` proves that two E0-equal two-ciphertext products
admit the direct or swapped pairing modulo E0. This conclusion retains both
factors, their multiplicities and their E0 equality. It follows from equality
of two-element multisets and exactness of the quotient. Rigid ciphertext
inversion then equates the relevant keys, nonces and plaintexts.
`homomorphic_root_outputs_base` handles the direct case by congruence and the
swapped case by commutativity of nonce composition and plaintext addition.

`root_outputs_base` combines the homomorphic and rigid analyses and proves:

```text
RootStep a b → RootStep a' b' → BaseEq a a' → BaseEq b b'
```

`root_peak_joined` exposes `ModuloStep a b`, `ModuloStep a b'` and
`JoinModulo b b'`. There is no `LocalConfluentModulo` premise. These joins also
lift through any common outer context using the existing context lemmas.
They do not yet classify distinct redex positions or E0 rearrangements that
change which factors a contextual rule consumes. The three-ciphertext and
variable-overlap results are separate ingredients in that remaining analysis.

Before the general proof, `HomomorphicRootExperiments.lean` checks a decidable
approximation: the multiset of factor head tags on every generating E0
fixture. All three seeds (1, 7, 42), each configured for 500 instances at maximum
size 40, pass with `gaveUp=0`; deterministic inputs 0–255 pass. The ordered-list
negative control fails at `n=0`, seed 1, zero shrinks. Tags do not decide E0
equality; the quotient theorem provides the stronger factor evidence.

`HomomorphicRootSPOT.swapped_ciphertexts_join` retains literal E7/AC routes
with unequal raw nonce order and a checked join.
`ordered_factors_not_invariant` proves the order counterexample for actual E0
classes and uses name separation to exclude a quotient that identifies all
atoms. Together with the rigid-root controls, these prevent raw syntax equality
or a constant observation from standing in for the intended property.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/HomomorphicRootExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
The combined structure/root build passes (3295 jobs). Public theorem types
retain their alignment premises; reported axioms are subsets of `propext`,
`Classical.choice` and `Quot.sound`. The final log has no warnings, errors,
custom axioms or `sorryAx`.


## Ordinary contextual rewriting

Status: machine-checked. This discharges ordinary nested and disjoint-position
peaks, without assuming the corresponding result for modulo-E0 steps.

`RawNormalization.lean` defines `normalizeRaw`: recursively normalize children,
then apply at most one raw root rule. `normalizeRaw_reachable` proves an actual
ordinary reduction trace from every input to its output.
`RootStep.normalize_eq` checks all seven rule schemata; repeated parameters
normalize identically. `Context.normalize_congr` lifts invariance through every
syntax context. Consequently `RewriteStep.normalize_eq` and
`RawReduces.normalize_eq` cover arbitrary ordinary reductions, including all
nested and disjoint positions.

Reachability plus invariance establishes idempotence. The checked decreasing
weight then rules out any ordinary rewrite from a normalized term.
`ordinary_rewriting_confluent` gives a literal common descendant for every pair
of ordinary reduction sequences. `raw_contextual_peak_joined` embeds ordinary
one-step peaks into the modulo join relation. Neither theorem assumes local
confluence or a restriction on variable types.

The relation names have distinct meanings:

| Relation | Allowed steps |
| --- | --- |
| `RawReduces` | Zero or more ordinary `RewriteStep`s |
| `Reduces` | Zero or more `ModuloStep`s, each of which permits E0 alignment |
| `ReducesModulo` | Modulo steps plus a final E0 equality, including the zero-step case |

Thus this result does not contradict `raw_confluence_false`, which refutes
literal joining for the existing `Reduces` relation. Nor does it discharge
`LocalConfluentModulo`.

`RawNormalizationSPOT` gives independent literal fixtures for two disjoint
projections and for decryption competing with projection inside its plaintext.
Each fixture exposes both first steps and reductions to its expected common
name or pair. The negative fixture uses
`dec(one, penc(pk(zero + one), name(1), name(0)))`.
Ordinary normalization leaves this term unchanged and it is raw-irreducible.
E3 nevertheless makes its keys match, allowing a modulo decryption to `name(0)`.
`raw_normalization_incomplete_modulo` proves that the normalized source and
endpoint are not E0-equal, using their distinct rigid heads. Raw normalization
therefore cannot replace the remaining background-alignment argument.

The directed gate runs before the general proof. All seven root fixtures and
nested test contexts preserve normalization, generated terms pass idempotence,
and nested decryption/projection returns an independently chosen name. Seeds
1, 7 and 42, each configured for 500 instances at maximum size 40, pass with
`gaveUp=0`; deterministic inputs 0–255 pass. The false E0-normalization claim
fails at `n=0`, seed 1, zero shrinks, and remains a checked counterexample.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/RawNormalizationExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3298 build jobs pass. The public types and axiom audit report only
subsets of `propext`, `Classical.choice` and `Quot.sound`; no warnings, errors,
custom axioms or `sorryAx` occur in the final build.

The remaining confluence task is to cover peaks whose redex placement or
matching changes across E0 representatives, including AC selection in larger
products. Ordinary contextual confluence, root overlap joins and the existing
three-ciphertext/variable joins are checked ingredients, not proof of this
coverage. Full-E constructor separation, nonce non-deducibility, accepted-ballot
characterisation and ballot secrecy remain separate open obligations.


## Factor reconstruction and arbitrary remainders

Status: machine-checked. The factor multiset is now complete for E0 equality,
and selected homomorphic pairs can be exposed in any source with those factors.

`FactorReconstruction.lean` equips the existing E0 quotient with multiplication
induced by the term constructor. Its commutativity and associativity follow
from the existing E0 equations. An auxiliary `WithOne` supports finite multiset
folds; its unit is bookkeeping only and has no object-language term or equation.
`Term.mulFactors_product` reconstructs the exact source class, and
`Term.mulFactors_nonempty` proves that no term corresponds to the empty bag.
`baseEq_iff_mulFactors` therefore gives both directions between E0 equality and
equality of the quotient factor multisets.

Every individual factor in a term's outer factor bag has a singleton-factor
representative. Multiplying representatives builds every nonempty submultiset
(`Term.subfactors_representable`). `homomorphic_selection_reachable` uses this
to produce an actual modulo step from any factor decomposition of the form
`{cipher₁, cipher₂} + rest`, together with the exact output bag
`{combinedCipher} + rest`. The pair uses one common encryption key. An empty
remainder is handled by the two-factor root theorem, without an added sentinel.
The quotient construction and representative existence are metatheory, not an
executable equality test or a new public-recipe operation.

`FactorSelectionOverlap.lean` proves the disjoint-selection peak for any source
containing two specified pairs plus any remainder. The pairs can use different
keys. After either first reduction, the other pair can still be selected. The
two descendants have equal factor bags and therefore are E0-equal. The shared
selection theorem similarly lifts the three-ciphertext peak to arbitrary
sources and remainders, using the checked nonce/plaintext associativity at the
endpoints. Both conclusions expose the first steps and the exact factor bag of
each branch, preventing a trivial choice of the same reduction twice.

The literal controls retain nonadjacent pair selection, a two-factor product
without a sentinel, two distinct-key groups, and a shared pair whose branches
both retain an unrelated name. Negative controls exclude treating zero as a
multiplicative unit, erasing a repeated factor, and combining different keys.
They derive expected outputs directly from E7 and the AC equations.

`FactorReconstructionExperiments.lean` checks nonempty flatten/rebuild mechanics,
pair rearrangement, multiplicity, empty-case handling, and two independent key
groups with both successful root outputs and wrong-key rejection. Each positive
property passes seeds 1, 7 and 42, configured for 500 instances at maximum size
40, with `gaveUp=0`; both deterministic backstops pass inputs 0–255. The false
zero-unit claim fails at `n=0`, seed 1, zero shrinks. The existing triple gate
supports the shared endpoint family. These executable checks precede the
corresponding general proofs and do not decide quotient equality.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/FactorReconstructionExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3301 jobs pass, including controls and the public-type/axiom audit.
The final log has no warnings, errors, custom axioms or `sorryAx`; only subsets
of `propext`, `Classical.choice` and `Quot.sound` are reported.

The following increment discharges arbitrary outer-fusion selection coverage.
Remaining coverage obligations are to relate all E0-dependent redex placements
to the checked cases and handle reductions inside factors whose matching
changes across E0 representatives. The checked factor lemmas do not by
themselves discharge `LocalConfluentModulo` or any full protocol privacy claim.


## Exhaustive outer-fusion joins

Status: machine-checked. `pair_selection_cases` classifies any two size-two
submultisets of a common source as identical, shared, or disjoint, supplying
explicit source decompositions in the latter cases. It preserves repeated
values. This is a classification of bags with valid occurrence realizations,
not recovery of syntax-position identities; realizations need not be unique.

`BagFusion` records the selected input bag, its rule output and the exact
retained remainder. `bag_fusion_diamond` proves a diamond for rules whose
inputs have size two, whose outputs are unique for each input bag, and whose
shared-input combinations associate. These three hypotheses are explicit.
`CipherFusion.rank`, `CipherFusion.deterministic` and `CipherFusion.associate`
prove them for the existing E7 rule on E0 ciphertext classes. The shared case
uses ciphertext constructor inversion to align key, nonce and plaintext
representatives. `cipher_fusion_diamond` therefore has no unproved rule-law
or confluence premise.

`OuterFusion a b` means that such a fusion replaces two outer factors of `a`
and yields exactly the factor bag of `b`. `realize_cipher_fusion` and
`OuterFusion.to_modulo` connect these bag witnesses to actual modulo steps.
`outer_fusion_peak_joined` takes any two `OuterFusion` witnesses from one term
and returns both specified modulo steps and a join of their endpoints.
It covers identical, shared and disjoint selections, arbitrary remainders,
repeated factors and different E0 representatives.

| Claim | Evidence | Scope |
| --- | --- | --- |
| Size-two selections admit an exhaustive bag decomposition | `pair_selection_cases` | Both selections are submultisets of the source and have cardinality two |
| Arbitrary outer ciphertext fusion peaks join | `outer_fusion_peak_joined` | Two `OuterFusion` hypotheses; internal factor reductions are outside this relation |
| Internal key simplification can enable fusion | `OuterFusionSPOT.internal_key_enables_fusion` | Literal contextual projection, unchanged factor count, failed source and successful target raw root matches |

The selection Plausible gate passes seeds 1, 7 and 42, configured for 500
instances at maximum size 40, with `gaveUp=0`; its deterministic backstop passes
0–255. The generator selects distinct indices within each pair and tests its
own size and inclusion obligations without discarded premises. The false
deduplication claim fails at `n=0`, seed 1, zero shrinks, and is retained as a
checked counterexample. Earlier triple and distinct-key controls supply the
independent E7 endpoint fixtures. `OuterFusionSPOT` adds repeated-factor joins,
raw matching failure with E0-equivalent keys, and proper-subrelation controls.
An internal projection in a ciphertext key enables an outer fusion while
preserving the outer factor count; the internal step itself cannot be a fusion.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/PairSelectionExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3306 jobs pass, with no warnings, errors or `sorryAx`; reported
axioms are subsets of `propext`, `Classical.choice` and `Quot.sound`.
The quotient bags remain metatheory and add no public recipe operation.

The following increment classifies arbitrary modulo steps and joins fusion
against any competing step. Arbitrary pairs of factor reductions, including
nonlinear matching within one factor, remain open. These results do not discharge
`LocalConfluentModulo`. Full-E constructor separation, nonce non-deducibility,
accepted-ballot characterisation and protocol privacy remain open.


## Outer fusion versus any modulo step

Status: machine-checked. `outer_fusion_modulo_peak_joined` proves
`JoinModulo b c` from `OuterFusion a b` and any `ModuloStep a c`. It requires
neither a supplied selection case nor local confluence.

The proof uses exhaustive ciphertext-step inversion: `ModuloStep.penc_cases`
shows that a step from `penc(k,r,m)` changes one component by a modulo step,
with its target equal modulo E0 to the corresponding updated ciphertext.
E0 changes in the other arguments are absorbed in this target equality.
`fusion_ciphertext_peak_joined` joins that step against E7. Key changes require
synchronizing the second key copy before fusion; nonce and plaintext changes
commute through E7's composition and addition constructors.

`FactorStep` selects a representative with a singleton outer factor bag, runs
one actual modulo step on it, and retains the exact remainder. It stores all
factors of the output term. This permits a projection to expand one factor into
a product. The generic `ModuloStep.of_factors` and `JoinModulo.of_factors`
transport steps and joins to arbitrary specified endpoint bags, reconstructing
nonempty remainders and handling empty ones without an added unit.
`fusion_factor_peak_joined` classifies whether the changed factor belongs to
the selected fusion pair or its remainder. The selected case uses ciphertext
inversion; the disjoint case commutes the two actions. Bag cancellation and
ciphertext orientation preserve multiplicity and E0 representatives.

`RewriteStep.factor_cases` exhausts all root-rule and context constructors.
A multiplication context adds to the remainder; another enclosing constructor
makes the whole term one factor. At an exposed root, E7 is an outer fusion and
the other rules have single-factor sources. `ModuloStep.factor_cases` lifts
this classification through the two E0 endpoint equalities. Combining the
fusion/fusion and fusion/factor results yields the stated theorem for an
arbitrary competing modulo step. The two classification cases need not be
exclusive.

| Claim | Evidence | Scope |
| --- | --- | --- |
| A ciphertext step changes one component modulo E0 | `ModuloStep.penc_cases` | An arbitrary `ModuloStep` whose source is a ciphertext |
| Fusion and single-factor reduction join | `fusion_factor_peak_joined` | Exact `OuterFusion` and `FactorStep` witnesses from one source |
| Every modulo step belongs to one of these classes | `ModuloStep.factor_cases` | All rules, contexts and E0 endpoint changes |
| Every peak with an outer fusion joins | `outer_fusion_modulo_peak_joined` | One `OuterFusion` and any competing `ModuloStep`; two factor steps remain open |

`CiphertextStepExperiments.lean` tests independently specified E7 outputs before
and after reachable component changes drawn from all seven root-rule families.
Seeds 1, 7 and 42 pass, configured for 500 cases at maximum size 40 with
`gaveUp=0`; the deterministic backstop passes inputs 0–255. The false one-key-copy
matching property fails at `n=0`, seed 1, zero shrinks. These tests cover the
executable component fixtures, not general quotient joinability.

`MixedFusionSPOT.lean` checks a selected nonadjacent ciphertext with an unrelated
name retained, both routes to a fixed synchronized-key endpoint, nonce and
plaintext changes, and E0 changes in an unchanged argument at the target. A
disjoint projection expands into two names; both remain in its factor bag. The
negative controls exclude raw matching after only one key copy changes and
relabeling the expanding factor step as a fusion.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/CiphertextStepExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3312 jobs pass, including controls and the public-type/axiom audit.
The log has no warnings, errors or `sorryAx`; all reported axioms belong to
`propext`, `Classical.choice` and `Quot.sound`. The factor relations remain
metatheory and grant no public ciphertext access.

The following increment proves disjoint factor joins and reduces local
confluence to the remaining singleton-source obligation. A single factor can be a whole non-multiplication term, so this case
includes root versus internal reductions and nonlinear fixed-constructor
matches. Full-E structure, nonce non-deducibility and protocol privacy remain
separate open obligations.


## Factor reduction peaks and the singleton obligation

Status: disjoint factor joins and the reduction to singleton-source local
confluence are machine-checked. `SingleFactorLocalConfluent V` remains unproved.

`singleton_selection_cases` classifies two selected factor classes while
retaining their exact residual bags. Equal selected classes give equal
residuals; the other case exposes a common disjoint remainder. The classification
preserves repeated values and does not identify unique syntax positions.
`disjoint_factor_reductions_joined` commutes two actual reductions of disjoint
subterms, allowing either output to expand into a product and preserving an
arbitrary remainder. Its source and branch bags identify both actions.

`FactorsLocallyConfluent source` requires local confluence for each singleton
representative whose class occurs in the source's factor bag.
`factor_peaks_joined_of_factor_local` uses this premise when the selected classes
are equal and the unconditional disjoint theorem otherwise. Adding the earlier
outer-fusion joins gives `modulo_peaks_joined_of_factor_local`.
`local_confluence_iff_single_factor` states the exact equivalence:

```text
LocalConfluentModulo V ↔ SingleFactorLocalConfluent V
```

The right-hand side requires joins for arbitrary modulo peaks whose source has
its singleton factor bag. This still includes active-root rules, internal
reductions and nonlinear matches. The equivalence does not prove that obligation
or supply it to the confluence or privacy theorems.

`locally_confluent_at_penc` handles one singleton constructor: explicit local
confluence at its key, nonce and plaintext implies local confluence at the
ciphertext. It uses exhaustive component inversion, including E0 changes in
unchanged components, and joins the component endpoints through the constructor.
`ciphertext_key_nonce_steps` separately checks unconditional commuting steps in
different components with a specified common ciphertext.

| Claim | Evidence | Remaining hypothesis or limit |
| --- | --- | --- |
| Disjoint factor reductions commute | `disjoint_factor_reductions_joined` | Two actual steps and exact source/branch factor bags |
| Factor peaks join when their selected representatives are locally confluent | `factor_peaks_joined_of_factor_local` | Explicit `FactorsLocallyConfluent source` premise |
| All source peaks join under the same premise | `modulo_peaks_joined_of_factor_local` | Same factor-local premise |
| Full local confluence is equivalent to the singleton-source obligation | `local_confluence_iff_single_factor` | Neither side is asserted unconditionally |
| Ciphertext local confluence follows from its components | `locally_confluent_at_penc` | Three explicit `LocallyConfluentAt` hypotheses |

`FactorPeakExperiments.lean` generates valid singleton selections and checks
both residual decompositions and full two-element replacement bags. Seeds
1, 7 and 42 pass, configured for 500 cases at maximum size 40, with `gaveUp=0`;
the deterministic backstop passes 0–255. The false strict-factor-weight property
fails at `n=0`, seed 1, zero shrinks: multiplication by zero preserves weight.
`factor_weight_need_not_decrease` retains this induction counterexample.

`FactorPeakSPOT.lean` uses independent E1 and E2 projections, each returning two
names, with an unrelated name retained. Both branches have four factors and
the specified common descendant has five; both actual second steps are checked.
A same-factor fixture changes key and nonce projections inside a ciphertext,
uses an E0-equivalent plaintext representative, and checks both routes to the
same literal endpoint. The branches differ syntactically. Repeated-value
fixtures retain all occurrences.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/FactorPeakExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3316 jobs pass, including campaigns, controls and the public-type/axiom
audit. The final log has no warnings, errors or `sorryAx`; reported axiom sets
are subsets of `propext`, `Classical.choice` and `Quot.sound`.

Next establish the singleton-source obligation, including the remaining
constructors and active-root versus internal reductions. An induction that
recurses into factors must justify strict descent; crypto weight alone does
not always provide it. Full-E structure, accepted-ballot characterisation and
privacy remain open. The factor predicates remain metatheory and do not alter
public recipes or ciphertext observations.


## Unary and passive rigid-binary constructors

Status: machine-checked constructor implications and unconditional projection
root/internal joins. Arbitrary argument local confluence remains a hypothesis.

`RootModuloStep` records a single root rule with E0 changes before and after it.
Its root/root endpoint equality follows from the earlier all-rule theorem.
`ModuloStep.unary_cases` classifies every step from a unary source as a root
rule modulo E0 or a reduction in its argument. `ModuloStep.rigid_binary_cases`
similarly classifies non-AC binary sources, with root, first-argument and
second-argument cases. Its `¬ AC f` premise is essential: ordered-argument
inversion does not apply to multiplication, addition or composition.

Pairing and partial-decryption construction have no root rule. The binary
inversion theorem retains a root alternative for active decryption.
`RootModuloStep.unary_projection_cases` restricts unary-root rules to fst/snd
on ordered pairs. Exhaustive pair-step inversion proves that a projection joins
every reduction inside its argument pair. Changes in the selected member are
followed on both routes; changes in the discarded member are erased.
`unary_root_inner_joined` includes arbitrary E0 representatives for those steps.

`locally_confluent_at_unary` handles fst, snd and pk under local confluence at
the argument. Root/root and root/internal peaks are already discharged; two
argument reductions use the explicit hypothesis. Pairing and partial-decryption
construction inherit local confluence from their two argument sources through
`locally_confluent_at_passive_binary`. Atomic irreducibility supplies base cases:
E0 preserves literal names and variables, so no step starts there; constants use
the earlier zero-weight theorem. These atom results alone have no nontrivial peaks.

| Claim | Evidence | Scope |
| --- | --- | --- |
| Unary steps are root or argument steps | `ModuloStep.unary_cases` | All unary operators and E0 representatives |
| Rigid binary steps are root or argument steps | `ModuloStep.rigid_binary_cases` | Explicit non-AC premise; active decryption retains its root case |
| Unary root/internal peaks join | `unary_root_inner_joined` | Unconditional for the supplied root and argument steps |
| Unary constructors preserve local confluence | `locally_confluent_at_unary` | Explicit argument local-confluence hypothesis |
| Passive binary constructors preserve local confluence | `locally_confluent_at_passive_binary` | Pairing or partial-decryption construction, with two argument hypotheses |
| Atoms are irreducible modulo E0 | `name_irreducible`, `var_irreducible`, `constant_irreducible` | Literal symbolic atoms; not full-E constructor separation |

`UnaryStepExperiments.lean` checks source-derived fst/snd outputs before and
after reachable changes in either member, using all seven root-rule families.
Seeds 1, 7 and 42 pass, configured for 500 cases at maximum size 40 with
`gaveUp=0`; the deterministic backstop passes inputs 0–255. The false claim that
fst and snd return the same member fails at `n=0`, seed 1, zero shrinks; the
literal expected outputs are names 0 and 1.

`UnaryLocalSPOT.lean` instantiates local confluence on a nested projection and
on partial-decryption construction with reducible arguments. Both have explicit
distinct first-step endpoints. The projection fixture checks the common literal
name reached by the two routes. Other controls cover all four member-selection
cases, independent E0 changes in root and internal targets, the failure of
pair commutativity modulo E0, and actual progress under pk despite failed root
matching. Thus the instantiated claims exercise more than the no-peak atom cases.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/UnaryStepExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3321 jobs pass, including campaigns, controls and the public-type/axiom
audit. The final log has no warnings, errors or `sorryAx`; reported axiom sets
are subsets of `propext`, `Classical.choice` and `Quot.sound`.

The remaining singleton analysis includes proof construction, active decryption
and proof checking, nonlinear matching, and the AC constructors. A global proof
must discharge the component hypotheses rather than assume them. The factor
weight counterexample still constrains the induction argument. Full-E structure,
accepted-ballot characterisation and privacy remain open; the new predicates and
constructor observations grant no public ciphertext access.


## Active decryption root/internal peaks

Status: machine-checked. Every E5/E6 root/internal peak joins, and
`locally_confluent_at_decryption` derives local confluence at `dec(a,b)` from
explicit local-confluence hypotheses at `a` and `b`.

`ModuloStep.pk_cases` classifies all steps from the public-key constructor as
argument steps. Combining this with ciphertext inversion gives
`ModuloStep.keyCiphertext_parameters`: every step from the E5/E6 ciphertext
pattern has an E0-equivalent target with synchronized key, nonce and plaintext
parameters reachable from their originals. `keyCiphertext` abbreviates the
existing `penc(pk(k),r,m)` pattern and adds no constructor or public operation.

The four canonical overlap theorems cover E5's explicit key and ciphertext,
and E6's left partial-decryption argument and right ciphertext. E6's left
argument inversion covers either its explicit key or its ciphertext copy.
After a field changes, the untouched repeated copies follow the same reduction.
Plaintext changes are also followed from the original root result. Each join
then uses the actual E5/E6 rule at the synchronized parameters, without a local
confluence assumption.

`RootModuloStep.decryption_cases` proves that every root instance at active
decryption is E5 or E6, with E0 equalities for both arguments and the result.
`decryption_root_left_joined` and `decryption_root_right_joined` transport the
canonical joins to arbitrary representatives. The generic rigid-binary
constructor theorem retains explicit root/internal hypotheses; the final
decryption theorem discharges both. Only the argument-local-confluence
hypotheses remain for competing internal reductions.

| Claim | Evidence | Scope |
| --- | --- | --- |
| Public-key ciphertext steps admit synchronized parameters | `ModuloStep.keyCiphertext_parameters` | Metatheory inversion of any step from the E5/E6 ciphertext pattern |
| E5/E6 roots exhaust active decryption roots | `RootModuloStep.decryption_cases` | Arbitrary E0 source and result representatives |
| Root decryption joins any left-argument step | `decryption_root_left_joined` | Both E5 and E6; no local-confluence hypothesis |
| Root decryption joins any right-argument step | `decryption_root_right_joined` | Both E5 and E6; no local-confluence hypothesis |
| Decryption inherits local confluence from its arguments | `locally_confluent_at_decryption` | Two explicit argument-local-confluence hypotheses |

`DecryptionExperiments.lean` checks independently expected E5/E6 outputs before
and after parameter changes drawn from all seven root-rule families. Seeds
1, 7 and 42 pass, configured for 500 cases at maximum size 40 with `gaveUp=0`;
the deterministic backstop passes inputs 0–255. The false claim that changing
one E6 ciphertext preserves raw root matching fails at `n=0`, seed 1, zero
shrinks, and is retained as a checked counterexample. These tests cover the
executable synchronization fixtures, not general quotient joinability.

`DecryptionSPOT.lean` checks all three field changes in either E6 ciphertext
copy and the explicit E6 key, with actual first steps and joins. E5's four
locations are checked too, and the field targets are proved distinct. The key
control checks failed matching with one or two updated occurrences, successful
matching after the third update, and the actual sequence to the fixed plaintext
name 2. A plaintext-copy control checks its updated endpoint independently.
A nontrivial E6 source with three reducible parameters has local confluence
without residual hypotheses and two distinct actual first-step endpoints. The
E0-only key fixture retains a failed raw root match alongside actual root and
nonce steps and their join.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/DecryptionExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3325 jobs pass, including campaigns, controls and the public-type/axiom
audit. The final log has no warnings, errors or `sorryAx`; reported axiom sets
are subsets of `propext`, `Classical.choice` and `Quot.sound`.

Proof construction, active proof checking, the AC constructor cases and the
global argument discharging component hypotheses remain open. Full-E structure,
accepted-ballot characterisation and privacy are not implied by these joins.
Parameter inversion is metatheory and does not expose private keys or ciphertext
fields to the public recipe language.


## Proof construction and checking

Status: machine-checked. Proof construction and checking inherit local confluence
from their components. Every checking root/internal peak joins unconditionally.
A source with an actual E8/E9 checking-root witness has local confluence without
component hypotheses.

Proof construction has no root rule. `ModuloStep.spk_cases` covers all four
argument positions with arbitrary E0 source and target representatives;
`locally_confluent_at_spk` uses four explicit component hypotheses. General
ternary inversion retains both a root-rule case and `TernaryArgumentStep`,
which records one actual argument reduction and the target's E0 equality.

The checking patterns repeat the key four times and the nonce three times.
`ModuloStep.bitCiphertext_parameters` classifies key/nonce updates and excludes
a step in the constant vote field. `ModuloStep.bitProof_parameters` additionally
synchronizes proof metadata and the bound ciphertext. A changed proof may need
further reductions before it matches; its conclusion exposes those reductions.
The three canonical checking lemmas update every remaining occurrence and then
apply the actual zero/one rule to reach ok.

`RootModuloStep.proof_check_cases` exhausts E8/E9, retaining the zero/one guard
and bound-ciphertext pattern. `proof_check_root_inner_joined` joins every root
with every argument step, across E0 representatives, with fixed result ok.
`locally_confluent_at_checkspk` therefore retains only its three component
hypotheses. Because ok is irreducible, `proof_check_step_reaches_ok` strengthens
the matching-source result: every competing single-step endpoint reduces to ok.
`locally_confluent_at_matching_check` derives local confluence from the actual
root witness alone. Arbitrary malformed or nonmatching sources are not covered
by this stronger theorem.

| Claim | Evidence | Scope |
| --- | --- | --- |
| Proof construction has four component-step cases | `ModuloStep.spk_cases` | Arbitrary E0 representatives; no proof-root rule |
| Proof construction inherits local confluence | `locally_confluent_at_spk` | Four explicit component hypotheses |
| Checking roots are the guarded E8/E9 patterns | `RootModuloStep.proof_check_cases` | Retains bit and bound-ciphertext requirements |
| Checking root/internal peaks join | `proof_check_root_inner_joined` | No local-confluence premise; actual root and argument steps |
| Checking inherits local confluence | `locally_confluent_at_checkspk` | Three explicit component hypotheses |
| Any step from a root-matching check still reaches ok | `proof_check_step_reaches_ok` | Actual checking-root witness and competing step |
| Root-matching checks are locally confluent | `locally_confluent_at_matching_check` | Actual root witness, without component hypotheses |

`ProofCheckingExperiments.lean` tests both bits with independently expected ok
results before and after reachable key/nonce changes from all seven root-rule
families. It rejects mismatched bound ciphertexts, wrong-bit proofs and fully
matching non-bit values. Seeds 1, 7 and 42 pass, configured for 500 cases at
maximum size 40 with `gaveUp=0`; the deterministic backstop passes 0–255. The
false binding-insensitivity claim fails at `n=0`, seed 1, zero shrinks, and is
retained as `mismatched_bound_ciphertext_no_match`. This gate tests executable
fixtures, not the general quotient join relation.

`ProofCheckingSPOT.lean` enumerates all four key and three nonce occurrences,
proves their source equalities and distinct target lists, and checks actual
steps followed by reductions to ok for both bits. A fixed route shows why the
last bound-ciphertext key cannot be omitted: raw checking fails before that
update and the actual checking rule follows it. Both bits instantiate local
confluence with real root steps. The E0 fixture expands all three zero vote
fields and retains both failed raw matching and a successful root/argument join.
A general proof-constructor fixture changes its third and fourth fields, checks
local confluence and two actual routes to a fixed endpoint. Those arbitrary
proof fields are not claimed to satisfy the ballot checking pattern.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/ProofCheckingExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3331 jobs pass, including campaigns, controls and the public-type/axiom
audit. The final log has no warnings, errors or `sorryAx`; reported axiom sets
are subsets of `propext`, `Classical.choice` and `Quot.sound`.

Every non-AC constructor now has its component implication. The remaining
confluence work is the AC analysis, particularly addition's zero/one equations
and nonce composition, and a global argument discharging the component
hypotheses. The factor-weight counterexample still constrains induction.
`SingleFactorLocalConfluent V`, full-E structure, accepted-ballot
characterisation and privacy remain open. All parameter observations and pattern
aliases are metatheory over the existing signature and add no public access to
proof or ciphertext components.


## Nonce-composition factors

Status: machine-checked factor reconstruction, step coverage and disjoint joins.
The same-factor local-confluence premise remains explicit.

`Term.composeFactors` flattens outer nonce composition into exact E0 classes,
retaining repeated values. E0 equality preserves the bag, including E0 changes
inside each factor. A private fold using a locally scoped composition semigroup
reconstructs the source class; `baseEq_iff_composeFactors` proves completeness.
The auxiliary `WithOne` identity represents only an empty bookkeeping bag.
`Term.composeFactors_nonempty` proves that every actual term has a nonempty bag,
and every nonempty subbag can be reconstructed as a term. The imported quotient
multiplication operation remains multiplication, as checked definitionally by
`multiplication_instance_unchanged`.

`ModuloStep.of_compose_factors` and `JoinModulo.of_compose_factors` lift steps
and joins through arbitrary remainders, handling the empty remainder without an
object-language unit. `ComposeFactorStep` records one singleton source factor,
its actual modulo step, and the complete output factor bag. Every raw rule source
is one composition factor; composition contexts extend its remainder. Therefore
`ModuloStep.compose_factor` covers every modulo step through arbitrary E0
representatives. A multiplication-root E7 step inside a composition context is
one such replacement, not a composition-root fusion.

`disjoint_compose_reductions_joined` commutes independent replacements with
arbitrary expanding outputs. Equal selected classes instead use
`ComposeFactorsLocallyConfluent source`, transported between E0 representatives.
`locally_confluent_at_of_compose_factors` then covers all peaks from the source.
This requires local confluence of its selected factors; it does not establish
that property for arbitrary factor terms. A representative interface and an
irreducible-factor theorem support later instantiations.

| Claim | Evidence | Scope |
| --- | --- | --- |
| Composition factor equality is exactly E0 equality | `baseEq_iff_composeFactors` | Exact quotient classes; no executable comparison claim |
| Nonempty remainders are representable | `Term.compose_subfactors_representable` | A nonempty subbag of an actual term's factors |
| Every modulo step replaces one composition factor | `ModuloStep.compose_factor` | All rules, contexts and E0 representatives; complete output bag retained |
| Disjoint composition replacements join | `disjoint_compose_reductions_joined` | Two actual steps and exact source/branch bags |
| All composition-source peaks join under factor local confluence | `locally_confluent_at_of_compose_factors` | Explicit `ComposeFactorsLocallyConfluent source` premise |

`ComposeFactorExperiments.lean` checks raw flatten/rebuild, AC permutations,
multiplicity, empty-case handling and projections expanding into two factors.
Seeds 1, 7 and 42 pass, configured for 500 cases at maximum size 40 with
`gaveUp=0`; the deterministic backstop passes inputs 0–255. The false zero-unit
claim fails at `n=0`, seed 1, zero shrinks, and is retained as a checked E0
counterexample. This is a representation-mechanics gate, not a quotient-equality
decision procedure.

`ComposeFactorSPOT.lean` retains two nonadjacent expanding projections and an
unrelated name. Both actual second steps reach the specified five-factor
endpoint. Controls cover an empty remainder, E0 changes within a selected
factor, repeated occurrences, and the absence of a unit. Multiplication and
composition of ciphertexts have different root behavior and are not E0-equal;
a nested multiplication step is classified correctly without changing the
composition-factor count. A source of independently locally confluent projection
factors instantiates local confluence with distinct actual first-step endpoints.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/ComposeFactorExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3336 jobs pass, including campaigns, controls and the public-type/axiom
audit. The final log has no warnings, errors or `sorryAx`; reported axiom sets
are subsets of `propext`, `Classical.choice` and `Quot.sound`.

At this increment, addition's zero/one analysis and the global discharge of
component and factor hypotheses remained open; the next section records the
subsequent addition representation proof. The composition analysis does not establish full
confluence, full-E structure, nonce non-deducibility or privacy. The new factor
observations and fold remain metatheory over the existing signature.


## Addition summaries

Addition now has an exact E0 representation. `Term.addSummary` stores a multiset
of non-numeric factor classes and an optional numeric count. `none` records no
numeric summand; `some 0` records a real zero; `some n` records n ones when n is
positive. This preserves zero beside a name and allows zero absorption beside
one. Repeated ones and non-numeric occurrences retain their multiplicities.

| Machine-checked claim | Declaration | Scope |
| --- | --- | --- |
| E0 preserves summaries | `BaseEq.add_summary` | All terms and contextual E0 equations |
| Equal summaries characterize E0 | `baseEq_iff_addSummary` | Summaries of actual terms |
| No term has the empty summary | `Term.addSummary_ne_empty` | Empty is bookkeeping only |
| Numeric counts have representatives | `addNumeral_summary`, `addNumerals_combine` | Natural counts, with E0 numeric equations |
| Occurring atoms have valid representatives | `Term.add_atom_representable` | Atom membership in an actual term summary |
| Nonempty summaries have representatives | `add_summary_representable` | Explicit valid-atom premise |
| Submultisets can be reconstructed | `Term.add_subsummary_representable` | Nonempty summary, atoms drawn from an actual term; any numeric part |

`AddSummaryExperiments.lean` checks AC combination, empty bookkeeping cases and
independently counted flat token lists. Seeds 1, 7 and 42 pass, configured for
500 cases at maximum size 40 with `gaveUp=0`; 256 deterministic inputs pass.
The false global-zero-identity and saturated-one properties both fail at n=0,
seed 1, zero shrinks. `AdditionSummarySPOT.lean` checks these counterexamples,
zero/one equations, repeated atoms, a mixed term with two ones, nested E0
representatives and the unchanged exported multiplication instance.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/AddSummaryExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3342 jobs pass; all 445 reported axiom sets are subsets of `propext`,
`Classical.choice` and `Quot.sound`, with no warnings, errors or `sorryAx`.
The summary is metatheory over the existing signature. It does not yet classify
addition steps or join their peaks. Those obligations and the global discharge
of component/factor hypotheses remain open, as do full-E structure and privacy.


## Addition replacement joins

Every modulo step reduces one non-numeric outer addition atom.
`ModuloStep.add_factor` proves this classification for arbitrary E0
representatives; `RewriteStep.add_factor` exhausts all seven rules and all
contexts. An addition context extends the retained remainder. Every other
context is part of the selected atom. No numeric-only source has a step.

| Machine-checked claim | Declaration | Scope |
| --- | --- | --- |
| Lift a specified step or join | `ModuloStep.of_add_summaries`, `JoinModulo.of_add_summaries` | Exact endpoint summaries; empty or representable nonempty remainder |
| Complete step classification | `ModuloStep.add_factor`, `AddFactorStep.to_modulo` | Actual selected step and complete output summary |
| Same or disjoint selected atom classes | `AddSummary.atom_selection_cases` | Atom cancellation; numeric cancellation is explicitly refuted |
| Disjoint replacements join | `disjoint_add_reductions_joined` | Arbitrary outputs and retained remainder |
| All addition-source peaks join | `locally_confluent_at_of_add_summaries` | Explicit `AddFactorsLocallyConfluent source` premise |
| Representatives supply the premise | `add_summaries_local_of_representatives` | Explicit locally confluent representatives |
| Numeric-only terms are irreducible | `irreducible_of_add_atoms_empty`, `addNumeral_irreducible` | All terms with no summary atoms; every numeral |

`AdditionReplacementExperiments.lean` checks atom cancellation, disjoint
replacement commutation and numeric presence. Seeds 1, 7 and 42 pass,
configured for 500 cases at maximum size 40 with `gaveUp=0`; 256 deterministic
inputs pass. The false numeric-cancellation property fails at n=0, seed 1,
zero shrinks; `AddSummary.numeric_cancellation_refuted` checks equal numeric
results from distinct remainder inputs.

The independent SPOT has two projections returning one and zero under addition,
with a name and a zero remainder. Both routes reach exactly one+name. It retains
distinct branches, changing numeric counts, the name, an empty remainder,
expanding outputs and an E0 representative change. Its projection factors also
instantiate local confluence for this actual source.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/AdditionReplacementExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3347 jobs pass, with 470 axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`. The final log has no warnings, errors or
`sorryAx`. The next obligation is a global argument supplying the component and
factor-local hypotheses; crypto weight alone does not strictly decrease into
every factor. Full confluence, full-E structure and privacy are still open.


## Global confluence

`GlobalConfluence.lean` proves local confluence by structural induction. The
induction carries locally confluent representatives of all multiplication and
composition factors and non-numeric addition atoms alongside local confluence
of the term. AC cases inherit representatives from child hypotheses; other
constructors use their component theorems and then supply singleton witnesses.
E0 transport handles arbitrary representatives of a factor class. No factor
crypto-weight descent or assumed confluence is used.

| Machine-checked claim | Declaration | Hypotheses |
| --- | --- | --- |
| Every term is locally confluent | `locally_confluent_at`, `local_confluence_modulo` | No confluence premise |
| Singleton-source obligation holds | `single_factor_local_confluence` | No confluence premise |
| All modulo reduction paths join | `confluence_modulo` | Two actual `ReducesModulo` paths |
| Irreducible descendants are unique modulo E0 | `normal_forms_unique_modulo` | Paths from one source and irreducible endpoints |
| Full E equality is joinability | `eqE_iff_join` | Arbitrary terms |
| Irreducible E equality is E0 equality | `irreducible_eqE_iff_base` | Both endpoints irreducible |

The three-seed mechanics gate passes (500 configured cases, maximum size 40,
`gaveUp=0`) and all 256 deterministic inputs pass. The false strict factor-weight
claim fails at n=0, seed 1, zero shrinks. The gate covers raw representative
inheritance and containment; the general proof supplies the unbounded result.
A checked mixed-constructor peak combines an E0-only decryption with a projection.
Both distinct branches reach the fixed expected descendant. Additional controls
preserve raw-normalization failure, distinct names, distinct zero/one constants
and the non-strict factor weight example.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/GlobalConfluenceExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3350 jobs pass, with 484 axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`; no warnings, errors or `sorryAx` appear.
This proves the relational confluence claim for the encoded symbolic theory.
It adds no executable equality decision procedure and does not establish nonce
non-deducibility, accepted-ballot characterization or ballot secrecy.
