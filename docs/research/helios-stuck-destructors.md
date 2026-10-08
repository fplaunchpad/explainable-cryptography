# Stuck projection and decryption observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Minimum initial-frame recipes with stuck fst/snd or
dec E-values have those exact outer operators. Full-E equality of stuck
projections preserves the selector and argument; equality of stuck decryptions
preserves both ordered arguments. These facts transfer first-world equalities
forward using strictly smaller public argument observations. The subsequent
[value-shape proof](helios-value-shapes.md) closes both minimum iff branches.
Full static equivalence remains open.

The origin theorems cover every positive candidate count, both swaps, arbitrary
caller name policies and all valid ground candidate substitutions, including
reducible representatives. They require neither freshness nor target normality.
The forward swap interfaces use the full restricted-name policy and retain the
unproved `Frame.ObservationsBelow` premise.

## Semantic stuckness and full-E equality

[StuckDestructorStructure.lean](../../ExplainableCrypto/Helios/Symbolic/StuckDestructorStructure.lean)
uses confluence and exhaustive destructor paths. Stuckness means absence of an
actual reachable match, rather than failure of raw syntactic matching:

- For a projection argument `a`, no `x,y` satisfy `a =E pair(x,y)`.
- For decryption arguments `a,b`, no `m` satisfies `DecryptionMatch a b m`.
  This relation includes delayed E5/E6 matches and their complete ciphertext
  binding.

Under the two no-pair premises,
`EqE.projection_iff_of_no_pair` proves
`f(a) =E g(b)` iff `f = g` and `a =E b`, with both selectors in fst/snd.
Under the two no-match premises, `EqE.decryption_iff_of_no_match` proves
`dec(a,b) =E dec(c,d)` iff `a =E c` and `b =E d`.
`stuck_projection_not_eqE_decryption` separates these two stuck output classes.
Arguments can reduce arbitrarily within full E; none must already be normal.

## Exact minimum origins

[StuckDestructorOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/StuckDestructorOrigins.lean)
first chooses an irreducible representative of the supplied stuck value. A
private head-classification proof considers every recipe constructor. Existing
normal-shape theorems exclude arithmetic and passive constructors. Minimum
decryptions cannot reach E5/E6. Successful minimum projections select honest
ciphertexts, proofs or nonempty tails, excluding a stuck destructor target.
A projection whose head survives retains its precise selector.

`Historical.General.minimum_stuck_projection_form` therefore derives
`r = unary f b`, with the same target selector `f`. Its conclusion also proves
that the recipe argument's evaluated value cannot equal a pair.
`minimum_stuck_decryption_form` derives `r = dec(u,v)` and rules out any reachable
decryption match for the evaluated ordered arguments. Both start from minimum
public size, a supplied E-value and semantic stuckness of that target. Normality
is internal to the proof.

## Forward transfer and the remaining reverse direction

`minimum_stuck_projection_equality_imp` and
`minimum_stuck_decryption_equality_imp` take two first-world minimum recipes,
one supplied stuck target for the first recipe, their first-world equality,
and the smaller-observation hypothesis at bound `|r|+|s|`. Equality supplies the
same stuck target for the other recipe, so the origin theorems classify both.
Injectivity then obtains equal first-world arguments. Each argument comparison
is public and strictly below the original bound. The bounded hypothesis
transfers those comparisons, and congruence gives equality of the destination
outputs.

The destination destructors need not remain stuck for this forward argument.
The public conclusions are implications, not iff statements. If an output
acquires a match in the destination, equality there need not imply argument
equality. The smaller whole-check/ok probe used for proof checks has no proved
counterpart here. No destination no-match premise, minimum-size premise or new
public operation has been added to bypass this obligation.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Stuck projections preserve selector and argument | machine-checked | `EqE.projection_iff_of_no_pair` | Both semantic no-pair premises; fst/snd selectors |
| Stuck decryptions preserve ordered arguments | machine-checked | `EqE.decryption_iff_of_no_match` | No reachable E5/E6 match on either side |
| Stuck projection and decryption outputs differ | machine-checked | `stuck_projection_not_eqE_decryption` | Both semantic stuckness premises |
| Minimum stuck-projection values force exact syntax | machine-checked | `General.minimum_stuck_projection_form` | Initial frame, caller policy, minimum size, stuck target value |
| Minimum stuck-decryption values force exact syntax | machine-checked | `General.minimum_stuck_decryption_form` | Same scope, ordered arguments and derived source no-match |
| Projection equality transfers forward | machine-checked | `General.minimum_stuck_projection_equality_imp` | Source minima/equality, stuck target and smaller public tests |
| Decryption equality transfers forward | machine-checked | `General.minimum_stuck_decryption_equality_imp` | Same source-only premises; no destination stuckness assumption |
| Full static equivalence | conjectured | Open task | Reverse direction, arbitrary-recipe closure and final frames remain required |

## Controls and executable scope

[StuckDestructorSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/StuckDestructorSPOT.lean)
contains ten public controls. Reducible name wrappers establish expected stuck
values while different selectors and reversed dec arguments remain unequal.
The known-defect witnesses are kernel-checked: fst of `(one,zero)` and
`(one,one)` agrees despite unequal arguments; E5 decryptions of nonce-50 and
nonce-51 ciphertexts agree despite unequal ciphertexts. An E6 companion also
reaches the independently specified zero plaintext.

Fst of the election-key handle is an exact two-node minimum. Dec of two public
literal names is an exact three-node minimum for every valid candidate
assignment in the fixture. Literal zero is a minimum with a successful
destructor E-value but different raw syntax, showing why target stuckness is
required. A public projection wrapper around a stuck decryption has the same
value but is nonminimum, showing why minimum size is required for exact origins.
A public wrong key cannot match an honest ciphertext even with arbitrary
argument reduction and a reducible honest bit. Separate controls distinguish
stuck selectors, ciphertext arguments and projection versus decryption heads.

The two forward interfaces are exercised with actual minima and reducible
supplied targets. These particular instances compare each recipe with itself
in diagonal-candidate frames; they establish that the premises are inhabited.
They are not evidence for transfer of a nontrivial pair of different recipes.
The general implication proofs quantify over arbitrary source minima, and the
separate unequal-output controls rule out constant-output semantics.

`StuckDestructorExperiments.lean` first detects both omitted-stuckness mutations
at input 0, seed 1, zero shrinks. Three positive families run at seeds 1, 7 and 42,
500 configured cases each, size 40, with `gaveUp=0`, followed by 256 deterministic
inputs covering all three checks. Projection tests vary both selectors and
public names with reducible arguments. Decryption tests vary both ordered
public names with reducible arguments. Wrong-key tests use actual initial
frames with one through five candidates, both swaps, abstention versus
candidate-zero selection and honest ciphertext selectors. They inspect raw
normalized outputs; this finite campaign does not decide full E or prove
privacy. The general full-E claims have kernel proofs.

## Reproduction and evidence boundary

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/StuckDestructorExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3495 jobs), including 17 new public theorem type/axiom
audits. Its 1309 nonempty axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`; another 17 reports are axiom-free. No warnings, errors or `sorryAx`
occur. The local log is `tmp/variable-overlap/stuck-destructor-full-build.log`.
The source audit covers 340 public theorem entries and selected stale claims in
20 current-status documents; it does not replace elaboration or prove log
freshness.

Trusted definitions remain E/E0, actual reduction paths and matching, public
recipes, node-count minimum size and the general initial frames. The reality
oracle is the source's ordered E1/E2 projections and E5/E6 key/ciphertext binding,
as recorded in the [symbolic model](helios-symbolic.md). No equation, public
operation, custom axiom or confluence assumption changed.

The subsequent [partial-key probe results](helios-decryption-probes.md) derive
destination failure and two-sided equality transfer for minimum decryptions
with partial-decryption and ciphertext source argument values. Other
decryption argument classes and stuck-projection reverse transfer are handled
by the later [value-shape results](helios-value-shapes.md), which derive
destination failure and complete both minimum iff branches. Arithmetic values,
arbitrary nonminimum evaluation transport and the global smaller-observation
premise remain open. Final frames publishing partial decryptions and historical process
matching remain required. See the preceding
[destructor observation record](helios-destructor-observations.md),
[static-equivalence interfaces](helios-static-equivalence.md) and canonical
[task list](../../task%20list.md).
