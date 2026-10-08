# Minimum value shapes and destructor equality

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Pair, ciphertext and partial-decryption value classes
are preserved across the initial-frame swap for a source minimum recipe under
public observations strictly below its own size. Simultaneous shape reflection
rules out newly enabled E5/E6 matches for every minimum decryption and newly
enabled pair selection for minimum stuck projections. Both stuck-destructor
minimum equality branches now transfer in both directions.

The theorems cover all positive candidate counts and all valid ground candidate
substitutions under the full name policy, including reducible representatives.
They assume source minimum size and the explicit smaller-observation hypothesis.
They require neither freshness nor destination minimum size, and the final
decryption failure theorem has no argument-shape premises. Arithmetic equality,
arbitrary nonminimum evaluation transport and the global observation hypothesis
remain open. These results do not establish full static equivalence.

## What shape means

[ValueShapeTransfer.lean](../../ExplainableCrypto/Helios/Symbolic/ValueShapeTransfer.lean)
defines three semantic predicates on terms:

| Predicate | Meaning |
| --- | --- |
| `Term.PairValue t` | Some `a,b` satisfy `t =E pair(a,b)` |
| `Term.CiphertextValue t` | Some `k,r,m` satisfy `t =E penc(k,r,m)` |
| `Term.PartialValue t` | Some `k,c` satisfy `t =E partialDecrypt(k,c)` |

The predicates classify full-E values, not raw heads. Their witnesses need not
be normal, and corresponding components need not agree across worlds. A checked
honest ciphertext example retains its ciphertext shape while changing its
plaintext and hence its ciphertext E-value.

`projection_chain_shape_reflection` uses exact initial-frame tuple positions.
Pair-valued chains are nonempty ballot tails, ciphertext-valued chains are
honest component selectors, and no initial handle chain has a partial-decryption
value. These facts hold across both swaps without minimum size or an observation
hypothesis.

For source minimum recipes, pair and partial values also transfer forward from
their established exact origins. Minimum ciphertext values have assembly syntax.
Smaller public key comparisons transfer assembly coherence, giving a destination
ciphertext value without requiring pointwise equality of the components.

## Simultaneous reflection

[MinimumValueShapes.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumValueShapes.lean)
proves `Historical.General.minimum_value_shape_reflection` by structural
induction on a minimum public recipe. Its conclusion reflects each of the three
destination value classes to the corresponding source class. Each child is a
minimum subterm, and its observation bound fits below the parent's size.

For projections, a destination value of one of these constructors implies an
actual pair path in the argument. The induction hypothesis reflects that pair
value to the source. Source minimum projection origins then force a handle
chain, whose tuple position determines the same class in either world.

For multiplication, a destination ciphertext value gives ciphertext values for
both operands. The child hypotheses reflect those values to the source. Their
minimum origins recover exact assembly syntax. The destination value supplies
key coherence for the assembled product; smaller key observations reflect that
coherence to the source. This permits homomorphic products without assuming
that the source operands initially use a common key.

For decryption, a destination match supplies a ciphertext value for its second
argument. The child hypothesis reflects that shape, and minimum origins recover
a ciphertext assembly. An E5 match is detected by comparing the assembly's
public key recipe with `pk(a)`, where `a` is the decryption argument. This test
is strictly smaller than the whole decryption. It transfers to a source E5
match, contradicting source minimum size.

An E6 match also supplies a partial-decryption value for the first argument.
The other child hypothesis reflects that shape. The previously checked
[partial-key probes](helios-decryption-probes.md) then rule out the destination
match. All three value-class implications therefore close in one induction;
none assumes the reflection result being proved for the whole recipe.

Other constructor cases use full-E separation or their literal constructor
values. Successful checks can return ok, but cannot produce any of the three
classified constructors, so no additional check-success premise is needed.
`minimum_value_shapes_swap` combines reflection with forward transfer to give
three iff statements under observations below the original recipe size.

## Complete minimum destructor branches

`minimum_decryption_failure_swap` applies the simultaneous theorem to the two
minimum arguments of any minimum `dec(a,b)`. It derives absence of every
reachable destination E5/E6 match. The earlier requirement to supply source
partial-key and ciphertext values is discharged. This theorem also covers
named arguments, stuck destructors as arguments and nested recipes.

[MinimumDestructorTransfer.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumDestructorTransfer.lean)
then proves:

- `minimum_no_pair_swap`: a minimum argument with no source pair E-value cannot
  acquire one under observations below that argument's own size.
- `minimum_decryption_equality_swap`: two syntactic source minimum decryptions
  transfer equality in both directions. Source and destination no-match facts
  justify ordered argument injectivity, and both argument tests are smaller.
- `minimum_stuck_decryption_equality_swap`: supplied stuck decryption E-values
  force exact raw origins before applying the complete syntactic branch.
- `minimum_stuck_projection_equality_swap`: supplied stuck fst/snd E-values
  force the exact selectors and arguments. Shape reflection preserves no-pair
  facts, then injectivity retains both selector identity and argument equality.

The value-based branches retain source minima, supplied source stuck values and
`Frame.ObservationsBelow` at the original comparison's total size. Supplied
values may have reducible arguments. Neither branch assumes destination
normality, constructor values, stuckness or minimum size.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic.Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Initial handle-chain value classes reflect across assignments | machine-checked | `projection_chain_shape_reflection` | Exact chain and initial frame; no observation premise |
| Minimum pair/partial value classes transfer forward | machine-checked | `minimum_passive_values_forward` | Source minimum size; exact origins |
| Minimum ciphertext class transfers forward | machine-checked | `minimum_ciphertext_value_forward` | Source minimum and smaller coherence tests |
| Destination pair/ciphertext/partial classes reflect together | machine-checked | `minimum_value_shape_reflection` | Structural induction; source minimum and observations below recipe size |
| All three value classes are invariant | machine-checked | `minimum_value_shapes_swap` | Three iff statements; components may change |
| Every minimum decryption remains unmatched | machine-checked | `minimum_decryption_failure_swap` | No source argument-shape certificates or destination minima |
| Minimum non-pair arguments remain non-pair | machine-checked | `minimum_no_pair_swap` | Semantic no-pair premise and smaller observations |
| Minimum decryption equality transfers both ways | machine-checked | `minimum_decryption_equality_swap` | Arbitrary minimum decryption arguments |
| Stuck-decryption value branch transfers both ways | machine-checked | `minimum_stuck_decryption_equality_swap` | Exact origins derived from source values |
| Stuck-projection value branch transfers both ways | machine-checked | `minimum_stuck_projection_equality_swap` | Both selectors and argument values retained |
| Full static equivalence | conjectured | Open task | Arithmetic equality, arbitrary-recipe closure and final frames remain required |

## Controls and executable scope

[ValueShapeSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ValueShapeSPOT.lean)
contains seven public controls. A two-node honest ciphertext minimum preserves
shape across selected-candidate versus abstention assignments, while its E-value
changes. One-node ballot handles and three-node partial constructors instantiate
the other two positive classes. Three-node name/name and six-node
partial/honest-ciphertext decryptions instantiate the general failure theorem.
Distinct name-based decryptions and different selectors over the election key
instantiate the complete iff branches and retain unequal outputs. One supplied
projection target has a reducible argument.

A public nonminimum E5 recipe and a successful projection both produce the
independently specified partial value, refuting universal destructor stuckness.
The secret-key-policy counterexample decrypts a vote, uses it as a ciphertext
key and fuses a product in only one world. This recipe violates the full public
policy; no minimum-size claim is made for it. It is a negative control for the
executable shape family, not a claimed counterexample to the minimum theorem
with only its policy premise removed.

`ValueShapeExperiments.lean` detects both known defects at input 0, seed 1, zero
shrinks. The positive shape family passes seeds 1, 7 and 42, each with 500
configured cases, size 40 and `gaveUp=0`, followed by 4096 deterministic inputs.
The generator uses one through five candidates, selected candidate zero versus
abstention, public names, all three handles and every term constructor, with
recipe depth one through three plus indexed selectors. It compares raw
normalized pair/ciphertext/partial tags; all other raw heads share tag zero.
It does not decide full E, certify recipe minimum size or supply the bounded
hypothesis. General full-E shape reflection and destructor failure have separate
kernel proofs.

Diagonal candidate assignments supply the bounded hypothesis for the larger
transfer controls. The two-node ciphertext control uses the empty range of
public comparisons strictly below size two, so it applies directly to different
votes without assuming their static equivalence.

## Reproduction and remaining work

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/ValueShapeExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3504 jobs), including 18 new public theorem type/axiom
audits and three definition checks. Its 1342 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; another 17 reports are axiom-free.
No warnings, errors or `sorryAx` occur. The local log is
`tmp/variable-overlap/value-shape-full-build.log`. The source checker covers 373
public theorem audit entries and selected stale claims in 22 current-status
documents; it does not replace elaboration or establish log freshness.

Trusted definitions remain E/E0, reachable matches, public recipes, node-count
minimum size, the actual initial frames and established exact origins/coherence.
The reality oracle is the source's E1/E2 projections, E5/E6 key and binding rules,
homomorphic key agreement and restricted initial secret key/nonces. No equation,
public operation, custom axiom or confluence assumption changed.

The subsequent [composition branch](helios-composition-observations.md) derives
semantic factor conditions and transfers composition equality from smaller
leaf tests. The [addition branch](helios-addition-observations.md) also now
transfers equality with exact numeric presence/count and atom multiplicity.
The [non-ciphertext multiplication branch](helios-multiplication-observations.md)
now transfers equality through smaller public fusion groups in both worlds.
Arbitrary nonminimum evaluation transport and the global smaller-observation
premise remain open.
Shape invariance does not give equality of vote-dependent components. Final frames publishing partial decryptions and
historical process matching remain required. See the preceding
[decryption probe record](helios-decryption-probes.md),
[static-equivalence interfaces](helios-static-equivalence.md) and canonical
[task list](../../task%20list.md).
