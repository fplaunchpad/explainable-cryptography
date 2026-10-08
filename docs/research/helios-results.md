# Checked Helios attack experiments

The first milestone establishes replay and permutation counterexamples in a
finite symbolic model. It also checks that ciphertext-component weeding blocks
these witnesses while accepting fresh ballots. The [historical symbolic foundations](helios-symbolic.md) now extend the
term and observation vocabulary beyond the finite experiment. There is no
general Helios ballot secrecy theorem or computational security reduction in
this artifact.

## Claim ledger

All declarations below are in `ExplainableCrypto.Helios`. The trusted definitions are in
[Model.lean](../../ExplainableCrypto/Helios/Model.lean): `valid`, `check`, `secrets`, `plaintext`,
`tally`, `run`, `RestrictedPrivacy` and the restricted `Recipe` interface.
The [model specification](helios-model.md) records the abstraction boundary,
source sections and independently derived arithmetic fixtures.

| Claim | Status | Formal oracle | Scope |
| --- | --- | --- | --- |
| Original policy hides the swapped choices | Refuted, machine-checked | `original_not_private`, `replay_accepted`, `replay_tallies`, `replay_distinguishes` | One fixed replay recipe and public tally test |
| Whole-ballot duplicate rejection hides the choices | Refuted, machine-checked | `wholeBallot_not_private`, `permutation_accepted`, `permutation_tallies`, `permutation_distinguishes` | One fixed permutation recipe |
| Swapping preserves the ideal validity check | Machine-checked | `swap_preserves_validity` | Every `Ballot` in this model; not a cryptographic proof-system theorem |
| Component weeding blocks selected attacks | Machine-checked | `components_block_replay`, `components_block_permutation` | Both worlds and either honest target |
| Fresh ballots remain acceptable | Machine-checked | `fresh_ballots_accepted`, `ordinary_tallies`, `fresh_abstention_tallied` | Three finite policies; fresh symbolic allocations |
| Controls exclude degenerate implementations | Machine-checked | `ordinary_not_rejected`, `tally_not_constant`, `malformed_rejected`, `malformed_not_tallied`, `component_rejection_not_invalid_proof` | Reject-all, constant-tally and wrong-rejection explanations |
| Valid vote encoding contributes at most one | Machine-checked | `issued_aggregate_at_most_one` | All finite private vote assignments |
| Full repaired protocol preserves privacy | Unresolved | No theorem | See [repair discrepancy](helios-repair-ambiguity.md) |

The falsifiers use three voters and two candidates. Copying Alice contributes
her vote twice; swapping her components contributes the opposite candidate.
The positive controls publish `(2,1)` for a fresh X vote and `(1,1)` for fresh
abstention. These expectations come from the source protocol's one-hot encoding
and arithmetic, not from the Lean evaluator. The abstract public ciphertext
handles do not change across swapped worlds; only the final tally distinguishes
the attack runs.

## Property-based refutation gate

[Experiments.lean](../../ExplainableCrypto/Helios/Experiments.lean) uses Plausible's decorated
binders and explicitly inspects `TestResult`. Unexpected failure, `gaveUp`, or
success of the known-broken claim causes an evaluation error and build failure.

The negative control runs first, seed 1: equality of the public replay test in
the two worlds. It finds a counterexample at `w = true`, with zero shrinks.
The named `replay_distinguishes` theorem retains the decisive witness.

Three positive campaigns use seeds 1, 7 and 42, each configured for 500 instances
and maximum size 40. All nine runs succeed, with `gaveUp = 0`:

- swapping preserves validity for generated submissions;
- fresh ballots are accepted by generated policies;
- component weeding rejects either selected attack against either target.

Natural numbers are reduced modulo 3 or 4 to generate finite votes, policies
and recipe forms; Booleans generate worlds and targets. There are no premise
filters. These distributions are not claimed to be uniform over elections or
to cover arbitrary symbolic adversaries. The malformed constructor is an
intentional negative-control submission. Deterministic backstops are
`recipe_swap_validity`, `fresh_ballots_accepted`, `components_block_replay` and
`components_block_permutation`. Successful campaigns are validation evidence,
not proofs of secrecy.

## Reproduction and trust audit

Validation: the finite milestone originally passed in 3269 jobs; the renamed
library plus symbolic foundations and documented correction pass in 3277 jobs. Run from the
repository root, with the pinned Lean/Mathlib 4.32.0:

```sh
lake build
lake env lean ExplainableCrypto/Helios/Experiments.lean
lake env lean ExplainableCrypto/Helios/Audit.lean
```

[Audit.lean](../../ExplainableCrypto/Helios/Audit.lean) checks the public types and prints the
axioms of every theorem in Replay, Permutation and SPOT. Reported dependencies
are subsets of `propext`, `Classical.choice` and `Quot.sound`; none reports
`sorryAx` or a custom cryptographic axiom. The attack privacy refutations use
only `propext`. The property-test harness is executable validation outside
these theorem proofs. No theorem uses `native_decide`.

Residual assumptions include ideal certificates, distinct symbolic allocations,
the fixed voter order, trusted tallying, two candidates and the restricted
recipe language. No equivalence to the full applied-pi process, concrete
ElGamal implementation or full decryption transcript has been proved. Upstream
VCVio/CatCrypt builds and the computational library decision remain separate
open tasks.
