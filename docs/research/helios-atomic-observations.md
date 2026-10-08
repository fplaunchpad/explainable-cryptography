# Atomic equality observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. A minimum public recipe with a name or constant E-value
in the actual initial frame is exactly that literal name or constant. Its value
is therefore preserved literally in any other frame with the same recipe type.
Equality of two such minima transfers across swapped worlds without a freshness
or smaller-observation premise. Arbitrary nonminimum recipe transport and full
static equivalence remain open.

The initial-frame results cover every positive candidate count, both swaps and
all valid ground candidate representatives, including reducible terms. The
origin and exact-transport theorems retain an arbitrary caller name policy. The
final swap interface uses the full restricted-name policy.

## Exact names, constants and minimum syntax

[AtomicObservationOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/AtomicObservationOrigins.lean)
proves `EqE.const_iff`: all four constant symbols are distinct under full E.
`name_not_eqE_const` also separates the two kinds of atom. Names already have
full-E injectivity. The public `EqE.ground_atoms_iff` combines these cases: for
two ground terms with node count one, E-equality is literal equality. Ground
terms have no variables, so the size condition describes exactly names and
constants, not arbitrary one-node recipes with handles.

`Historical.General.frame_handle_not_atom` excludes every initial handle. The
public-key handle has a pk value, while the two ballot handles have nonempty
pair values; neither can equal an irreducible ground atom. This proof allows
reducible candidate representatives.

`frame_name_deducible_iff` gives an exact name-deducibility boundary under the
caller's policy:

```text
There exists a public recipe r with eval(r) =E name(x)
if and only if x is outside the restricted-name set.
```

The forward direction uses protected-value non-deducibility for all recipes.
The reverse direction supplies the public literal name. It does not infer
non-deducibility from a bounded search or assume protection invariant under
arbitrary E-expansion.

Thus a minimum recipe with a name value has a public one-node competitor.
Constants always provide one-node public competitors. Minimum size forces the
original recipe to have at most one node. Excluding handles and distinct atoms
then proves `minimum_name_form` and `minimum_constant_form`, with exact raw
recipe equalities in their conclusions.

## Equality transfer

[AtomicObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/AtomicObservationInduction.lean)
uses those exact forms to prove `minimum_atomic_eval_any_frame`. Its source
recipe must be minimum in the actual initial frame and E-equal to a supplied
ground atom. Its destination can be any frame with three handles and the same
name policy. The conclusion is literal evaluation equality with the supplied
atom, because the classified recipe contains no handles.

`minimum_atomic_equality_iff` applies this result to two recipes and reduces
their equality test in any destination frame to literal equality of their
supplied atoms. `minimum_atomic_equality_swap` specializes the conclusion to
the two candidate assignments. It assumes first-world minima and atomic
E-values, but no preserved minimum size, second-world value, freshness or
`ObservationsBelow` hypothesis.

This result concerns minimum recipes for atomic values. A nonminimum recipe
that evaluates to an atom still needs a separate evaluation-transport argument;
replacing it by a minimum recipe in one world does not establish equality with
that replacement in the other world.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Full-E atomic equality is literal equality | machine-checked | `EqE.const_iff`, `EqE.ground_atoms_iff` | Four constants, unbounded names, ground one-node targets |
| Initial handles have no atomic E-value | machine-checked | `General.frame_handle_not_atom` | All three handles and arbitrary valid candidate representatives |
| A name is deducible exactly when it is public | machine-checked | `General.frame_name_deducible_iff` | Actual initial frame, arbitrary caller policy, all recipes |
| Minimum atomic recipes have literal syntax | machine-checked | `General.minimum_name_form`, `General.minimum_constant_form` | First-world minimum and supplied E-value |
| Minimum atomic values survive any destination frame | machine-checked | `General.minimum_atomic_eval_any_frame` | Atomic source value; destination shares three-handle recipe type and policy |
| The atomic minimum-recipe branch transfers equality | machine-checked | `General.minimum_atomic_equality_swap` | First-world minima/values; no smaller-observation or freshness premise |

## Independent controls and executable gate

[AtomicObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/AtomicObservationSPOT.lean)
contains eight theorem controls. Every public literal name and all four constants
attain the one-node minimum in either fixture world. E3/E4 give nonliteral sums
with zero or one values, while zero and one remain unequal; each sum has a
smaller public literal. An actual successful honest component-proof check
returns ok and is not minimum, including with reducible candidate values.

The retained omitted-minimum failure is the one-candidate gate fixture: secret
key 0, auxiliary name 1, voter nonces 2 and 3, left abstention and right selection
of candidate zero. Its three-step tail from the first ballot returns bottom and
is not minimum. Both swaps are checked. A projected public name 40 likewise has
a nonminimum wrapper; name 41 remains unequal to its value.

An arbitrary frame publishing name 40 at a handle admits a minimum handle for
that atomic value. Replacing its published value with name 41 changes the
handle's result. This counterexample demonstrates why the source initial-frame
premise is essential. In contrast, a literal minimum derived from the initial
frame retains its value in that replacement frame.

The nonce-only policy permits literal secret key 10 as a one-node minimum;
the full policy excludes every recipe deducing that name. The complete atomic
swap interface is instantiated in the actual different-vote worlds by two
unequal one-node minima, name 40 and constant zero, without a bounded-observation
premise.

`AtomicObservationExperiments.lean` first detects omitted minimum size and
constant collapse, both at input 0, seed 1, zero shrinks. The positive gates
pass seeds 1, 7 and 42, each with 500 configured cases, size 40 and `gaveUp=0`,
plus 784 deterministic inputs. The generators use actual frames at one through
five candidates and both swaps, with left abstention and right candidate-zero
selection. They check non-atomic handles, projected public names, successful
component checks, empty tails, and ordered identity/type comparisons for the
four constants and seven public names.

Expected output atoms are specified independently: ok for the successful
component check, bottom for the empty tail, and the literal argument for a pair
projection. These raw-normalization gates do not check E3/E4; the arithmetic
controls above are separate kernel-checked full-E statements. The gates are not
a complete E-equality decision procedure or proof of arbitrary-recipe privacy.

## Reproduction and remaining work

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/AtomicObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3486 jobs), including 20 new public theorem type/axiom
audits and four definition checks. Its 1274 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; another 17 are axiom-free. No
warnings, errors or `sorryAx` occur. The local log is
`tmp/variable-overlap/atomic-observation-full-build.log`. The source audit checks
305 public theorem entries and selected stale claims in 18 current-status
documents; it does not replace elaboration or establish log freshness.

Trusted definitions remain E/E0, distinct term constructors, public recipes,
minimum node counts, general initial frames and protected-name semantics. The
reality oracle is the source signature and initial key/ballot frame, E3/E4 bit
sums, E8/E9 proof checking, and the documented finite tuple tail. No equation,
public operation, custom axiom or confluence assumption changed.

The subsequent [destructor observation results](helios-destructor-observations.md)
now classify successful minimum projections and establish the stuck-check-valued
minimum branch. Arithmetic and other stuck value heads, arbitrary evaluation transport and the global
observation premise remain open. Final frames publishing partial decryptions
and process matching still require proofs. The complete objective remains in
the canonical [task list](../../task%20list.md). See the preceding
[pair branch](helios-pair-observations.md) and
[static-equivalence interfaces](helios-static-equivalence.md).
