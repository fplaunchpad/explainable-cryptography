# Expanded stuck projections and decryptions

Status: machine-checked under the stated numeric-result and smaller-observation
premises. Arbitrary source-minimum recipes with stuck-projection or
stuck-decryption values now have exact destructor syntax. Their equality
observations transfer across the vote swap. Stuck projections of minimum
children and stuck decryptions of minimum children are also minimum.

These results close two local B8 value branches. The global observation premise,
remaining value branches and shared-minimum induction are still open.

## Shared origins and actual expanded handles

[StuckMinimumTools.lean](../../ExplainableCrypto/Helios/Symbolic/StuckMinimumTools.lean)
defines `Term.StuckDestructorHead` and proves three generic frame-relative
lemmas: `minimum_normal_stuck_head_of_origins`,
`minimum_stuck_projection_form_of_head`, and
`minimum_stuck_decryption_form_of_head`. The premises expose successful minimum
projection data, minimum decryption no-match, and handle exclusions. They are
proved for the actual frames rather than assumed globally.

The common head argument normalizes the target, classifies the minimum recipe,
and retains the exact selector or ordered decryption head. It then excludes
successful source arguments. Full E is used throughout; target arguments may
reduce, and failed raw matching is not a substitute for the no-match premises.
[StuckDestructorOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/StuckDestructorOrigins.lean)
now reuses these helpers for the initial-frame proof, preserving its public
statements.

[ExpandedStuckOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedStuckOrigins.lean)
proves the expanded handle exclusions. Old handles have key or pair values;
partial handles retain their partial constructor; accepted result values are
numeric. None supplies a normal stuck-destructor head. Successful minimum
projections still select honest data, and whole minimum decryptions cannot
match in the source. The public results are:

- `expanded_minimum_stuck_projection_form`: exact `fst`/`snd` syntax and a
  source argument with no pair E-value.
- `expanded_minimum_stuck_decryption_form`: exact ordered decryption syntax
  and source no-match.
- `expanded_minimum_stuck_projection_of_child`: minimum closure for a minimum
  child whose value cannot be a pair.
- `expanded_minimum_stuck_decryption_of_children`: minimum closure for minimum
  children whose decryption does not match.

These origin and closure statements preserve the caller's public-name policy
as a separate parameter and assume numeric results only in the source world.
The target no-pair/no-match conditions are essential. They are not replaced by
target normality assumptions.

## Equality transport

[ExpandedStuckTransport.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedStuckTransport.lean)
provides accepted-election interfaces for arbitrary source-minimum recipes:

- `accepted_expanded_minimum_no_pair_swap` uses the checked pair-shape
  equivalence to retain a failed projection argument.
- `accepted_expanded_minimum_stuck_projection_equality_swap` derives both
  origins and destination no-pair facts, then compares the exact selectors
  and their arguments.
- `accepted_expanded_minimum_stuck_decryption_equality_swap` derives both
  origins and reuses the checked syntactic decryption equality theorem.

Fresh names and sequentially accepted public submissions discharge the numeric
result premises. Both equality branches use observations strictly below the
sum of the two original recipe sizes. The decryption case derives destination
E5/E6 failure using the existing whole-decryption/result-handle probes: each
other decryption has at least three nodes, which pays the explicit probe
allowance. No recipe-only decryption failure theorem is claimed. Neither
branch assumes destination minimum size or full expanded static equivalence.

## Controls and refutation gate

[ExpandedStuckSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedStuckSPOT.lean)
retains nine controls:

1. Actual size-two stuck selectors and size-three stuck decryptions are minimum
   in both expanded assignments.
2. The accepted projection-equality interface distinguishes `fst` from `snd`
   in a diagonal election with an inhabited observation premise.
3. The accepted stuck-decryption interface distinguishes unequal named keys
   under the same diagonal premise.
4. Origin classification accepts a target whose argument actually reduces.
5. A projection wrapper has a stuck-decryption value but is nonminimum and has
   a different raw head, preserving the minimized counterexample.
6. Successful projections forget unselected data, so stuck injectivity cannot
   apply to them.
7. A one-node published result is minimum and has an actual successful E6
   expression as its value, despite lacking decryption syntax.
8. A newly published partial handle supplies a minimum non-pair argument for
   either stuck selector.
9. A successful E5 wrapper returns a stuck-decryption payload and is nonminimum.

The historical projection, E5 and E6 equations determine the independent
expected behaviors; no equation or publication value changes. Full E, recipe
size/publicness, expanded frames and accepted-election semantics remain trusted.

[ExpandedStuckExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedStuckExperiments.lean)
detects both mutations at input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 each
pass 500 cases at size 40 with `gaveUp=0`; 2048 deterministic inputs pass.
The generator covers both candidates and assignments, partial/result-based
arguments, both selectors, named failed decryption arguments, and successful
projection/E5 wrappers. This is executable behavior evidence on the generated
family; it does not certify universal minimum size or decide full E.

## Verification and remaining scope

The gate passes 1021 jobs. The initial shared-head refactor passes 842 jobs,
expanded origins and closure pass 933 jobs, and equality transport passes 941
jobs. The [results ledger](helios-results.md) records final control/build results
and the type/axiom audit, including the unchanged initial-frame callers. Full
`lake build` passes 3675 jobs, with 2051 nonempty standard-only axiom reports,
20 axiom-free reports, 1085 public theorem entries and 58 current-status docs.
Nineteen new theorem audits include all nine controls; one definition check is
added. Log: `tmp/variable-overlap/expanded-stuck-full-build.log`.

[Expanded composition](helios-expanded-composition.md) now closes that local
equality branch and minimum closure. [Expanded addition](helios-expanded-addition.md)
now supplies its conditional equality branch with numeric result handles.
[Addition minima](helios-expanded-addition-minima.md) now close addition shared
minimum transport. Remaining B8 work includes multiplication/ciphertext
observations, remaining shared minima and global observation induction. Successful projection
and decryption cases must also be integrated into that induction; these
stuck-value theorems alone do not cover all operators. The
[blueprint](helios-proof-blueprint.md) remains at seven of ten completed
milestones (70% unweighted), with historical process matching and full symbolic
secrecy open at B9/B10.
