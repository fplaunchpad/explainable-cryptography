# Addition equality from smaller summand observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. Full-E addition equality is characterized by exact
nonnumeric atom multiplicities and an optional numeric count when every atom
has no addition, zero or one E-value. Minimum initial-frame recipes derive
these atom conditions in both worlds. Their addition-valued equality branch
transfers in both directions from strictly smaller public observations.

The result covers every positive candidate count and every valid ground
candidate substitution under the full name restriction. Supplied summands may
reduce. The theorem retains both source minimum-size premises and
`Frame.ObservationsBelow` at the original total recipe size. It does not require
freshness, destination minimum size or pointwise agreement of summand values.
The subsequent [non-ciphertext multiplication branch](helios-multiplication-observations.md)
also transfers equality through smaller public fusion groups. Arbitrary-recipe
closure and full static equivalence remain open.

## Full-E summary accounting

[FullAdditionSummary.lean](../../ExplainableCrypto/Helios/Symbolic/FullAdditionSummary.lean)
defines `Term.addValueSummary : Term V → AddSummary (FullClass V)`.
It flattens raw outer addition, places zero and one in the numeric component,
and records each other leaf's full-E class as an atom. `none` means that no
numeric summand was present. `some 0` retains a present zero; `some n` retains
the exact number of ones. Repeated nonnumeric atoms retain their multiplicity.

`FullClass.AddAtom` excludes addition values and both numeric constant values.
`Term.AtomicAddFactors` requires this property for each recorded atom. Atoms
may reduce: a projection exposing a name satisfies the condition, while a
projection exposing zero or a compound addition does not. Zero and one also
have addition E-values through E3/E4, so their explicit exclusions agree with
the source theory.

`ModuloStep.add_value_summary` uses the existing exact outer-factor step
classification. A semantic atom cannot reveal numeric material or additional
summands, and its replacement retains the same full-E class. Actual modulo
paths therefore preserve the entire summary. Confluence compares both paths,
giving `eqE_iff_add_value_summary` under both atom premises.

Conversely, `eqE_of_add_value_summary` reconstructs E-equal terms from equal
summaries without atomicity assumptions. Its auxiliary fold uses an adjoined
identity only for bookkeeping; it adds no public unit or equation. Even a
literal zero has a nonempty summary (`Term.addValueSummary_ne_empty`). The
full-E quotient is metatheory, not an executable equality procedure.

## Minimum origins and substitution

[MinimumAdditionOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumAdditionOrigins.lean)
proves `minimum_add_form`: an addition-valued minimum recipe is raw addition,
literal zero or literal one. This statement keeps both legal numeric collapses.
The source result permits either swap and arbitrary caller name policies.

`minimum_add_form_after_swap` derives the same alternatives for a destination
addition value from source minimum size and smaller observations. Preserved
decryption failure and reflected pair values exclude active destructor
exceptions. Successful honest selectors publish pairs, ciphertexts or proofs,
which cannot supply an addition value. No target normality is assumed.

[AdditionLeaves.lean](../../ExplainableCrypto/Helios/Symbolic/AdditionLeaves.lean)
records the raw recipe skeleton with `Term.addSyntaxSummary`. Literal numeric
material stays in its numeric field; nonnumeric leaves stay in its atom bag.
Each such leaf is a genuine minimum public subterm and has neither raw addition
nor numeric constant syntax. The origin theorems therefore exclude addition
E-values in both worlds, which also excludes zero and one E-values.

`minimum_add_leaf_values` derives both worlds' semantic atom conditions.
`Term.add_leaves_substitution` then proves exact evaluated summary accounting:
map the raw nonnumeric leaves to their evaluated E-classes and retain the
original numeric component. It also supplies `AtomicAddFactors` for the whole
evaluated term. Neither result requires substituted recipes to be irreducible.

## Equality transfer

[AdditionObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/AdditionObservationInduction.lean)
proves `Historical.General.minimum_addition_equality_swap`. Its public premises
are the actual initial frames, two source minimum public recipes, supplied
source addition E-values, and `Frame.ObservationsBelow` at their total size.

Each nonnumeric leaf of an addition/bit recipe is strictly smaller than that
recipe. Smaller public leaf comparisons transfer equality of the full-E atom
multisets, preserving multiplicity. Numeric components are fixed by the raw
recipe skeletons, so their comparison is identical in both worlds. This gives
the full equality iff through the exact summary characterization.

Literal zero/one minima have empty atom bags and participate in the same proof.
This is necessary: zero is E-equal to zero+zero and one to zero+one, but a minimum
recipe for either constant need not have an addition head. The theorem does
not prove the global smaller-observation premise or transport arbitrary
nonminimum evaluations.

## Controls and verification

[AdditionObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/AdditionObservationSPOT.lean)
contains eleven public controls. They retain reducible mixed-sum reconstruction,
both legal numeric collapses, observable present zero, two distinct ones,
repeated atoms, and separate failures from hidden numeric/additive values.
Public literal name sums have exact three-node minima for arbitrary valid
candidate assignments, including repeated names. Distinct permuted minima and
unequal multiplicity minima instantiate the complete transfer theorem. Their
six-node bounded premises use diagonal candidate assignments.

A separate one-node zero/one control instantiates the complete addition branch
in different-vote worlds at the base bound of two. It retains unequal outputs
and reducible supplied addition values. A public nonminimum wrapper demonstrates
why the exact-origin theorem needs its minimum-size premise.

`AdditionObservationExperiments.lean` first detects hidden numeric material and
deleted numeric presence at input 0, seed 1, zero shrinks. Both have checked
counterexamples. The positive proxy gate passes seeds 1, 7 and 42, each with
500 configured cases, size 40 and `gaveUp=0`, plus 5120 deterministic inputs.
The generator includes names, public keys, pairs and stuck projections, revealed
through reducible wrappers; numeric contributions range from zero through four.
Expected atom occurrences and numeric counts are specified independently.
These tests compare raw-normalized executable summaries, not arbitrary full-E
observations. General equality has separate kernel proofs.

```sh
lake build
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/addition-observation-full-build.log
```

The addition increment's full build passes 3516 jobs, including 27 new public theorem type/axiom
audits and four definition checks. It reports 1394 nonempty axiom sets using
only `propext`, `Classical.choice` and `Quot.sound`, plus 17 axiom-free reports.
No warnings, errors or `sorryAx` occur. The source checker covers 425 public
theorem audit entries and 24 current-status documents; it does not replace
elaboration or establish build-log freshness.

Trusted definitions remain E/E0, actual modulo paths, public recipes, node-count
minimum size and the general candidate frames. The reality oracle is the
source's AC addition and equations E1–E4: projection can reveal a hidden value,
zero+zero and zero+one collapse, and no global zero identity or positive-count
saturation is specified. No equation, public operation, custom axiom or assumed
confluence changed.

The [non-ciphertext multiplication branch](helios-multiplication-observations.md)
also now transfers equality through smaller public fusion groups. Arbitrary
nonminimum evaluation transport and the global smaller-observation premise
remain open. Final frames
publishing partial decryptions and historical process matching remain required.
See the preceding [composition record](helios-composition-observations.md),
[static-equivalence interfaces](helios-static-equivalence.md) and canonical
[task list](../../task%20list.md).
