# Composition equality from smaller factor observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Full-E equality of compositions with semantically
indivisible factors is exactly multiset equality of their factor E-classes.
Minimum initial-frame recipes derive the required factor conditions in both
candidate worlds. Their composition-valued equality branch therefore transfers
in both directions using strictly smaller public leaf comparisons.

The swap theorem covers all positive candidate counts, all valid ground
candidate substitutions and arbitrary reducible target components under the
full name policy. It retains source minimum size and `Frame.ObservationsBelow`
at the original comparison's total node count. It assumes neither freshness,
destination minimum size nor pointwise equality of factor values across worlds.
The subsequent [addition branch](helios-addition-observations.md) also transfers
minimum equality. The [non-ciphertext multiplication branch](helios-multiplication-observations.md)
also now transfers equality through smaller public fusion groups.
Arbitrary-recipe closure remains open; full static equivalence is not established.

## Full-E factors and multiplicity

[FullCompositionFactors.lean](../../ExplainableCrypto/Helios/Symbolic/FullCompositionFactors.lean)
defines `FullClass` as the quotient by the existing `EqE` relation.
`Term.composeValueFactors` flattens raw outer composition into a multiset of
these classes. It preserves every repeated occurrence. This quotient supports
metatheory accounting; it is not an executable full-E equality test or a public
protocol operation.

A class satisfies `FullClass.ComposeAtom` when it has no E-equal representative
of the form `compose(a,b)`. `Term.AtomicComposeFactors` requires this property
for every factor. Such factors can still reduce. A projection revealing a name
is permitted; a projection revealing a composition is not an indivisible factor.

The existing exact modulo-step classification selects one composition factor
and replaces it by the factors of its reduct. If the selected factor has no
composition E-value, its reduct cannot have a composition head. Its replacement
bag is therefore one occurrence of the same full-E class. Induction over actual
paths preserves the whole factor bag, including multiplicities. No intermediate
normal-form premise is needed.

`eqE_iff_compose_value_factors` combines these two path invariants with confluence:

```text
AtomicComposeFactors(a) and AtomicComposeFactors(b) imply
  a =E b iff composeValueFactors(a) = composeValueFactors(b).
```

Both factor conditions are explicit. The reverse implication,
`eqE_of_compose_value_factors`, needs neither condition: folding equal bags in
the composition semigroup reconstructs equal full-E classes. The auxiliary fold
identity is internal to the proof; no unit is added to the term language.

## Exact minimum origins in either world

[MinimumCompositionOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumCompositionOrigins.lean)
proves `Historical.General.minimum_compose_form`: a source minimum recipe with
a composition E-value has literal `compose(a,b)` syntax. This origin theorem
retains an arbitrary caller name policy and either source swap. Target
components need not be normal.

For the full-policy swap,
`minimum_compose_form_after_swap` derives that same raw syntax from a destination
composition E-value and a source minimum recipe under smaller observations.
It uses the already checked preservation of decryption failure and argument
pair shapes. A successful minimum projection selects honest tuple data, whose
class cannot be composition. A retained projection or decryption keeps its
other head. Proof checks return either a retained check or ok. The remaining
constructors are excluded by full-E arithmetic/constructor separation.

Thus a minimum raw leaf with a non-composition head has no composition E-value
in either world. Destination minimum size is not needed for this conclusion.

## Raw leaves and public equality tests

[CompositionLeaves.lean](../../ExplainableCrypto/Helios/Symbolic/CompositionLeaves.lean)
defines `Term.composeLeaves`, the multiset of raw outer-composition leaves.
`composeLeaves_mem` supplies a genuine one-hole context for each leaf and proves
that its raw head is not compose. Context node counts bound each leaf by its
recipe; every leaf of a nontrivial composition is strictly smaller than the tree.
Minimum size and publicness pass to these actual subterms.

`minimum_compose_leaf_values` applies the exact origin results to each minimum
leaf, deriving its semantic indivisibility in both frames. The generic
`Term.compose_leaves_substitution` then identifies the evaluated term's full-E
factor bag with the mapped raw leaf bag. It also proves the semantic factor
conditions required by the full-E equality theorem. No factor certificate is
assumed in the final swap interface.

[CompositionObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/CompositionObservationInduction.lean)
transfers equality of these bags using the smaller public observations.
Multiset equality is lifted equality between corresponding occurrences, so
preserving the equality relation between members preserves bag equality without
losing duplicates. Each left/right leaf comparison is strictly below the original
total recipe size.

`minimum_composition_equality_swap` derives both raw composition origins, both
frames' semantic factor conditions and both bag representations. It transfers
the bag comparison and reconstructs full-E equality in the destination, and
also proves the reverse direction. The explicit global smaller-observation
hypothesis remains unproved. Leaves may use other constructors, including
addition or stuck destructors; their equality tests are smaller hypotheses,
not additional arithmetic results proved by this branch.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Equal quotient classes mean exactly full-E equality | machine-checked | `fullClass_eq_iff` | Existing congruence relation; no executable comparison |
| Modulo paths retain indivisible factor bags | machine-checked | `ReducesModulo.compose_value_factors` | Semantic factor condition on the source |
| Factor equality characterizes full-E equality | machine-checked | `eqE_iff_compose_value_factors` | Semantic factor conditions on both terms |
| Equal bags reconstruct equal terms | machine-checked | `eqE_of_compose_value_factors` | No indivisibility premise |
| Minimum composition values force compose syntax | machine-checked | `General.minimum_compose_form` | Source minimum, caller policy and supplied E-value |
| Destination composition values force source raw compose syntax | machine-checked | `General.minimum_compose_form_after_swap` | Source minimum, full policy and observations below recipe size |
| Raw leaves are actual smaller subterms | machine-checked | `Term.composeLeaves_mem`, `Term.compose_leaf_smaller` | Multiplicity retained; strict bound for nontrivial composition |
| Minimum leaves cannot reveal hidden compositions | machine-checked | `General.minimum_compose_leaf_values` | Both worlds; destination minimum size absent |
| The complete composition-valued minimum equality branch transfers | machine-checked | `General.minimum_composition_equality_swap` | Derived origins and factors; source minima and bounded observations |
| Full static equivalence | conjectured | Open task | Arbitrary-recipe closure and final frames |

## Controls and executable scope

[CompositionObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/CompositionObservationSPOT.lean)
contains eight public controls. Reducible factors, reassociation and permutation
preserve the independently specified three-occurrence bag. Duplicate deletion
is rejected under full E. A projection exposing a composition has one raw leaf
but two resulting factors: its E-value agrees with the exposed composition,
while the raw factor bags have different cardinalities. This is the checked
counterexample to omitting semantic indivisibility. A separate control preserves
addition's zero-plus-one equation while rejecting a zero unit for composition.

Public compositions of two literal names are exact three-node minima in actual
initial frames for arbitrary valid candidate assignments, including repeated
names. Distinct permuted minima instantiate the complete equality branch with
a reducible supplied target. Minima with changed multiplicity instantiate its
unequal case. A public nonminimum wrapper has a composition value with another
raw head, retaining the necessity of minimum size for exact origins.

`CompositionObservationExperiments.lean` detects hidden composition and
duplicate deletion at input 0, seed 1, zero shrinks. The positive family passes
seeds 1, 7 and 42, each with 500 configured cases, size 40 and `gaveUp=0`, followed
by 1024 deterministic inputs. It uses public names, public-key constructors,
pairs and stuck projections as factors, with reducible wrappers, permutation,
reassociation and duplicates. The checks compare raw-normalized leaf lists and
permutations; they do not decide full E or certify minimum size. Those claims
have separate kernel proofs. Diagonal candidate assignments supply the bounded
premise in swap controls, without assuming different-vote static equivalence.

## Reproduction and remaining work

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/CompositionObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The composition increment's full build passes (3510 jobs), including 25 new public theorem type/axiom
audits and seven definition checks. Its 1367 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; another 17 reports are axiom-free.
No warnings, errors or `sorryAx` occur. The local log is
`tmp/variable-overlap/composition-observation-full-build.log`. The source checker
covers 398 public theorem audit entries and selected stale claims in 23
current-status documents; it does not replace elaboration or establish log
freshness.

Trusted definitions remain E/E0, exact modulo paths, public recipes, node-count
minimum size and the actual initial frames. The full-E quotient and its bags
are defined from these existing relations. The reality oracle is the source's
AC composition without a unit or idempotence, together with E1/E2's ability to
expose compound values. No equation, public operation, custom axiom or assumed
confluence changed.

The [addition branch](helios-addition-observations.md) now retains exact numeric
presence/count and atom multiplicity through minimum equality transfer.
The [non-ciphertext multiplication branch](helios-multiplication-observations.md)
also now transfers equality through smaller public fusion groups. Arbitrary
nonminimum evaluation transport and the global smaller-observation premise
remain open.
Final frames publishing partial decryptions and historical process matching
remain required. See the preceding [value-shape record](helios-value-shapes.md),
[static-equivalence interfaces](helios-static-equivalence.md) and canonical
[task list](../../task%20list.md).
