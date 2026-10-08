# Proof-check values after publication

The expanded-frame stuck-check branch now derives exact check syntax and
transfers its equality observations under smaller tests. Successful minimum
projections still select old honest data. Stuck checks of minimum children are
minimum. These are B8 dependencies; failed-decryption reflection and the global
expanded-frame induction remain open.

## Successful projections

`expanded_minimum_successful_projection_form` starts from an actual source
minimum projection and a pair-valued argument. The expanded minimum pair and
selector origins force the argument to be an old ballot tail. A first
projection selects an honest field. A second projection must retain a
nonempty tail: the last second projection returns bottom and has a shorter
public literal recipe. The proof works under an arbitrary caller's minimum
policy and retains numeric results as its frame premise.

`ExpandedHonestProjectionForm.argument_pair_path` supplies an actual reduction
modulo E0 to a pair for either vote assignment. Its `data_value` theorem reuses
the existing honest projection classification through retained handle values.
The output is a nonempty tail, ciphertext or proof. These two consequences need
neither destination minimum size nor an observation hypothesis.

## Stuck checks

`Frame.minimum_normal_check_form_of_origins` extracts the original structural
argument. It requires that handles cannot supply the target normal check,
successful minimum projections return pair/ciphertext/proof data, and whole
minimum decryptions have no successful match. Both initial and expanded frames
instantiate it. The original public stuck-check theorem keeps its type; no
unproved frame premise is added to it.

In the expanded instance, old key and ballot handles and new partial handles
are separated from check values by their constructors. Numeric results cannot
have a normal stuck-check value. `expanded_minimum_stuck_check_form` first
normalizes the supplied stuck target, then uses the generic structural theorem.
The target's components may reduce; target normality is not assumed. Actual
accepted public elections discharge numeric results through the wrapper.

`expanded_minimum_stuck_check_of_children` proves constructor minimum closure
under actual failure. Every minimum competitor has check syntax. Full-E
injectivity for failed checks compares all three ordered arguments, and the
child minimum bounds imply the parent bound. Successful checks are excluded
from this closure claim because the public constant ok is shorter.

`expanded_minimum_stuck_check_equality_swap` derives both source recipe forms
and reuses `minimum_proof_check_equality_transfer`, which already supports
arbitrary handle counts. Source failure follows minimum size. Smaller tests
compare each whole check with ok and rule out a new destination match. Three
smaller argument comparisons then transfer equality. Destination failure and
minimum size are derived or unnecessary, not extra assumptions.

The accepted wrapper supplies numeric results but retains the intended
**smaller-observation premise**. Its global instance is still open. The
[expanded value-shape theorem](helios-expanded-value-shapes.md) now supplies
shape reflection and syntactic minimum-decryption equality. [Expanded stuck
values](helios-expanded-stuck-values.md) now add exact origins and both
stuck-value equality branches. Global observation induction remains open.

## Controls and evidence

Eight controls in `ExpandedCheckSPOT.lean` cover an actual minimum first
ciphertext projection with pair paths in either assignment; the nonminimum
empty-tail projection; successful E8 and E9 with nested published key/nonce
arguments and a shorter ok recipe; noninjectivity of successful checks;
rejection of a changed fourth proof binding under full E; an inhabited minimum
stuck-check equality step with a published partial key and unequal third
arguments; a nonminimum projection wrapper outside check syntax; and successful
structured-key E5 returning a stuck check through a nonminimum wrapper.

The gate detects successful-check injectivity and omitted-minimum wrapper
mutations at input 0, seed 1, with zero shrinks. Seeds 1, 7 and 42 each pass
500 cases at size 40 with `gaveUp=0`; 2048 deterministic inputs pass. Fixtures
cover both candidates and assignments, both proof bits, changed fourth
bindings and nested published partial/result key and nonce arguments. This
raw-normalization gate is bounded executable evidence, not a full-E decision
procedure.

The pre-proof gate passes 1017 jobs. The expanded projection target initially
passes 929 jobs; after the shared helper extraction, the expanded check target
passes 931 jobs. Logs: `tmp/variable-overlap/expanded-check-gate.log`,
`tmp/variable-overlap/expanded-successful-projection-check.log` and
`tmp/variable-overlap/expanded-check-origins-check.log`. All eight controls pass 1028 jobs. Full `lake build` passes
3660 jobs, with 2000 nonempty standard-only axiom reports and 20 axiom-free
reports. The checker covers 1034 public theorem entries and 55 current-status
documents. Seventeen new theorem audits include eight controls; one definition
check is added. Integrated log:
`tmp/variable-overlap/expanded-check-full-build.log`. The new modules are `CheckMinimumTools.lean`,
`ExpandedSuccessfulProjections.lean`, `ExpandedCheckOrigins.lean`,
`ExpandedCheckSPOT.lean` and `ExpandedCheckExperiments.lean`; the existing
`StuckCheckOrigins.lean` reuses the extracted structural proof.

The equations and public transcript definitions are unchanged. The
[blueprint](helios-proof-blueprint.md) remains at B8, seven of ten completed
milestones (70% unweighted). Remaining value branches, shared minima, global
observation induction, historical process matching and full symbolic secrecy
remain open.

[Expanded pair/selector transport](helios-expanded-pair-selector-minima.md) now
closes those three local roots without smaller-test premises. All local roots
and the simultaneous induction are assembled conditionally: successful
decryption/checking transport in both directions is the remaining requirement
for expanded, partial and final static equivalence.

[Expanded successful-check transport](helios-expanded-successful-checks.md) now
closes `checkspk`, retaining whole-ciphertext binding and exact honest combination
origins. The remaining local interface for all three frame presentations is
successful decryption in both directions; B8 local coverage is now 11/12.
