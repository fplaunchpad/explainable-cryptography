# Minimum projections and stuck proof-check observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. A successful minimum projection in the actual initial
frame selects an honest ballot field or retains a nonempty ballot tail. The
same syntax reaches an argument pair in either candidate world. Every minimum
recipe with a stuck proof-check E-value has explicit checkspk syntax, and its
equality with another such minimum transfers under `Frame.ObservationsBelow`.
The destination checks' failure is derived from smaller public tests.

These initial-frame results cover all positive candidate counts, both swaps and
all valid ground candidate representatives, including reducible terms. They do
not require freshness. Origin statements retain arbitrary caller name policies;
the final swap interface uses the full policy. Full static equivalence remains
open.

## Successful minimum projections

[MinimumProjectionObservations.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumProjectionObservations.lean)
uses the established pair origins to classify a minimum `fst(a)` or `snd(a)`
whose argument has a pair E-value. If `a` were a constructed pair recipe, the
projection would be a raw redex with a smaller public equivalent. The remaining
argument is a projection chain on an initial handle. Its pair value forces
exact ballot-tail syntax; the public-key handle cannot supply it.

`Historical.General.HonestProjectionForm n f a` states:

```text
For some voter i and offset k:
  k < fieldCount(n), a = snd^k(var(i+1)), and
  f = fst, or f = snd with k+1 < fieldCount(n).
```

The strict bound for snd excludes the empty result. That result would be E-equal
to public bottom, forcing literal bottom syntax by the atomic minimum theorem,
contradicting the projection head. `minimum_successful_projection_form` derives
this form from minimum size, a fst/snd symbol and the supplied argument pair
value. It does not assert that every indexed selector is minimum.

`HonestProjectionForm.argument_pair_path` reaches an actual argument pair for
any valid candidate assignment. The generic `EqE.reaches_pair` obtains a pair
path from a pair E-value without target normality. `HonestProjectionForm.data_value`
then classifies the output as a pair, ciphertext or proof. Fst selects the exact
field class; snd retains a nonempty tuple. This proves successful projection
structure across worlds, without asserting that vote-dependent output values
are unchanged.

## Stuck checking and smaller public probes

[ProofCheckObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/ProofCheckObservationInduction.lean)
proves `EqE.proof_check_iff_of_no_match`. If neither check can reach an E8/E9
match, full-E equality of the checks is exactly equality of all three ordered
arguments. The proof uses actual reduction paths and confluence. It does not
infer absence of a match from failed raw matching.

The existing `MinimalRecipe.no_proof_check_match` supplies failure in the source
frame: a successful check would have the smaller public representative ok.
To transfer failure, `Frame.ObservationsBelow.check_failure` compares the entire
checking recipe with literal ok. This public observation is equivalent to the
existence of a reachable E8/E9 match.

For checking recipes `r` and `s`, the probe `r =E ok` has total size `|r|+1`,
strictly below `|r|+|s|` because a checking recipe has more than one node. The
other probe is smaller for the same reason. Thus the bounded hypothesis rules
out either check acquiring a match in the destination frame. Each of the three
corresponding argument comparisons is also strictly smaller and public.

`minimum_proof_check_equality_transfer` therefore handles arbitrary source and
destination frames with a common handle type and name policy. It takes source
minima and the bounded hypothesis, and derives destination failure before
transferring component equality. It assumes neither destination minimum size
nor destination no-match witnesses. `minimum_proof_check_equality_swap` is its
initial-frame specialization.

## Arbitrary recipes with stuck-check values

[StuckCheckOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/StuckCheckOrigins.lean)
removes the syntactic origin premise from the value-based branch.
`minimum_stuck_check_form` takes a minimum public recipe whose E-value is
`checkspk(k,c,p)`, together with the absence of any reachable match for those
target arguments. The arguments may be reducible; target normality is not a
public premise.

The proof chooses a reachable normal representative of the stuck target.
Projections that retain their head cannot equal this check head. Successful
minimum projections produce the honest tuple data classified above, whose
heads also differ. Minimum decryption cannot reach E5/E6 by the existing
ciphertext-origin theorem. Arithmetic, key and other constructor cases are
excluded by their established normal-value shapes and full-E separation.
Only explicit checkspk syntax remains.

`minimum_stuck_check_equality_swap` derives both forms, then applies the checking
transfer. It retains first-world minima, supplied stuck-check E-values and the
global smaller-observation premise. No target normality, second-world origin,
minimum size or failure premise is assumed. A successful target check belongs
to the atomic ok case instead, so its no-match premise cannot be omitted.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Successful minimum projections have honest selector syntax | machine-checked | `General.minimum_successful_projection_form` | Minimum fst/snd recipe, actual argument pair value, initial frame |
| Classified projection arguments reach pairs in either world | machine-checked | `General.HonestProjectionForm.argument_pair_path` | Any valid candidate assignment; actual path in conclusion |
| Classified outputs are honest tuple data | machine-checked | `General.HonestProjectionForm.data_value` | Pair, ciphertext or proof; no empty snd result |
| Stuck checks compare all three ordered arguments | machine-checked | `EqE.proof_check_iff_of_no_match` | No reachable match on either side, arbitrary reducible arguments |
| A smaller ok probe preserves check failure | machine-checked | `Frame.ObservationsBelow.check_failure` | Public check and explicit strict size bound |
| Syntactic minimum checking equality transfers | machine-checked | `minimum_proof_check_equality_transfer` | Arbitrary frames, source minima and bounded hypothesis |
| A minimum stuck-check value forces check syntax | machine-checked | `General.minimum_stuck_check_form` | Initial frame, source minimum and nonmatching target value |
| The stuck-check-valued minimum branch transfers equality | machine-checked | `General.minimum_stuck_check_equality_swap` | Derived origins, source values/minima and bounded hypothesis |

## Independent controls and executable scope

[MinimumDestructorSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/MinimumDestructorSPOT.lean)
contains eight theorem controls. The first honest ciphertext projection is an
exact two-node minimum, and its classified argument reaches a pair in both
worlds. An early snd retains a nonempty tail; the final snd returns bottom and
fails the form's strict bound. A nonminimum projection of a constructed pair
returns the election key, retaining the omitted-minimum failure at the
one-candidate gate allocation.

A check of three public literal names is an exact four-node minimum in actual
initial frames, for arbitrary valid candidate assignments in the two-candidate
fixture. Its second argument is a name, so no ciphertext match is reachable.
Changing only the third argument from name 50 to 60 changes the stuck-check
value, preserving the input-0 ignored-proof-field counterexample.

Successful zero- and one-proof checks both equal ok despite distinct ciphertext
arguments. Literal ok is a one-node minimum for either successful-check value,
refuting removal of the stuck-value premise from the origin theorem. A separate
pair of frames changes a wrong proof to a matching proof; the whole-check/ok
probe detects the new match below the eight-node bound.

The complete value-based induction interface is instantiated by unequal
four-node checking minima at an eight-node total bound. One supplied target has
a reducible proof argument. Diagonal candidate assignments supply the bounded
hypothesis; this control does not assume different-vote static equivalence.

`MinimumDestructorExperiments.lean` detects omitted minimum size and ignored
proof fields at input 0, seed 1, zero shrinks. The positive projection and
checking-observer gates pass seeds 1, 7 and 42, each with 500 configured cases,
size 40 and `gaveUp=0`, plus 256 deterministic inputs. Generated frames use one
through five candidates, both swaps, left abstention and right candidate-zero
selection. The projection gate covers field kinds, nonempty tails and terminal
bottom. The checking gate compares correct and other-voter proofs and checks
both whole-check/ok size bounds. These raw-normalization families do not decide
full E or prove arbitrary-recipe privacy; the full-E claims have kernel proofs.

## Reproduction and remaining work

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/MinimumDestructorExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3491 jobs), including 18 new public theorem type/axiom
audits and four definition checks. Its 1292 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; another 17 are axiom-free. No
warnings, errors or `sorryAx` occur. The local log is
`tmp/variable-overlap/minimum-destructor-full-build.log`. The source audit checks
323 public theorem entries and selected stale claims in 19 current-status
documents; it does not replace elaboration or establish log freshness.

Trusted definitions remain E/E0, ordered tuple projection, public recipes,
node-count minimum size, actual general frames, reachable proof-check matches
and the existing minimum ciphertext origins. The reality oracle is the source's
ordered projections and E8/E9 binding, with the documented terminal-tail
correction. No equation, public operation, custom axiom or confluence assumption
changed.

The subsequent [stuck-destructor increment](helios-stuck-destructors.md) derives
exact minimum projection/decryption origins and forward equality transfer.
The later [value-shape proof](helios-value-shapes.md) derives destination
failure and closes both minimum iff branches. Arithmetic values, arbitrary
evaluation transport and the global smaller-observation premise remain open. Successful projection
structure alone does not prove equality of its vote-dependent fields. Final
frames publishing partial decryptions and process matching are also required.
The complete objective remains in the canonical [task list](../../task%20list.md).
See the preceding [atomic branch](helios-atomic-observations.md) and
[static-equivalence interfaces](helios-static-equivalence.md).
