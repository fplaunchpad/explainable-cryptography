# Helios development experience and evidence

This account distinguishes three outcomes: a completed symbolic proof, a checked
finite computational reduction, and an explicit decision to defer the stronger
machine-checked efficiency layer. The current computational conclusion uses the
external efficiency and attacker-membership arguments in the
[closing audit](helios-computational-closing-audit.md). Its revised milestone count
is 3/3; this does not mean that every deferred execution checkpoint is complete.
The [task list](../../task%20list.md) remains the only backlog.

## What the development established

The symbolic endpoint,
[`scopedVoterElection_ballot_secrecy`](../../ExplainableCrypto/Helios/Symbolic/SourceBallotSecrecy.lean),
proves source weak labelled bisimilarity for the repaired historical protocol
under its explicit freshness conditions. Public observations, rejection behavior,
and protocol correspondence are part of that result. It is not a computational
soundness theorem. The [reuse retrospective](helios-reuse-retrospective.md)
separately records which upstream transition-theory adapters were checked and
which proposed substitutions did not remove the local protocol obligations.

The computational development models concrete cryptographic algorithms and
probabilistic election games. Its finite reduction retains preparation, casting,
guessing, the shared random oracle, and explicit error terms. The subsequent
[`prepared_negligible_of_fair_bits`](../../ExplainableCrypto/Helios/Computational/ElectionSecrecyFairBits.lean)
transports the exact reductions to fair-bit sampling and derives query budgets;
it does not equate a query bound with a runtime bound.

A later coverage audit found that polynomial work in actual callback-input size
would not imply a security-parameter-only query cap on every arbitrary oversized
state. The repair is an actual query clock, accompanied by equality on reached
inputs. [`ElectionSecurityFamily.Family.coverage`](../../ExplainableCrypto/Helios/Computational/ElectionSecurityFamily.lean)
and `run_coverage` identify the original game and its clocked form, including
final shared storage. `Family.ballot_secrecy` then keeps four explicit hypotheses:
field-size negligibility, efficiency of the exact normalized main and rejection
reductions, and DDH against the chosen machine class. Main-reduction efficiency
is required separately for each fixed accuracy degree. The external arguments,
rather than a Lean backend adequacy theorem, justify the final efficiency boundary.

## Why execution was separated from the reduction

The execution work proved useful local results: arithmetic and encoding routines,
cache operations, a complete reusable proof-request executor, and a combined
caller that executes the same code for two distinct requests. General native
query export and one-call oracle round-trip theorems subsequently covered finite
tapes containing internal blanks, preserved private storage, and derived actual
instruction costs. These are stronger than output-only tests, but they do not
execute every election continuation or establish a general compiler theorem.
See [`PrimeRemainingProofCallerRun`](../../ExplainableCrypto/Helios/Computational/PrimeRemainingProofCallerRun.lean)
and [`NativeRoundTripCorrectness`](../../ExplainableCrypto/Helios/Computational/NativeRoundTripCorrectness.lean).

This work exposed a planning issue: proving another local controller did not by
itself settle the whole reduction's runtime or attacker coverage. The revised
strategy retains those checked artifacts and places the exact reduction-efficiency
claims in inspectable definitions in
[`ReductionEfficiency`](../../ExplainableCrypto/Helios/Computational/ReductionEfficiency.lean).
Each realization requires finite executable code, exact output-law correspondence,
and a polynomial bound on every path. It cannot replace callback or storage work
with an uncharged host operation. Deferring their construction is a scope decision,
not evidence that such constructions are impossible.

## What the pinned backend inspection found

The root VCVio pin **does contain an actual Turing-machine backend**:
[`Backend/TuringMachine.lean`](../../external/VCVio/VCVioComplexity/VCVioComplexity/Backend/TuringMachine.lean)
provides concrete deterministic machine certificates and exact terminating runs.
At this pin, its header explicitly distinguishes this from general composition
instances, oracle-machine adequacy, and an unqualified PPT claim. Root PolyFun
also supplies quantitative closure machinery. The local positive control
[`CompositionalEncrypt.realizer`](../../ExplainableCrypto/Helios/Computational/CompositionalEncrypt.lean)
composes the actual encryption expression from supplied efficient primitive
realizers. Thus the finding was not an absence of compositional infrastructure.

An isolated newer-pin experiment constructed executable caller/handler microsteps,
retaining suspended caller state and dependent replies. It did not construct a
complete quantitative substitution witness. Newer PolyFun's `IterationCode`
requires a uniform executable iterator and a cost decomposition; `polyRealizer`
then derives a polynomial bound from count, initial-size, additive-growth, and
administrative-cost premises. Merely finding that theorem did not supply the
required iterator instance or the bounds for this composed dispatcher.

The remaining construction obligations were executable normalization of silent
handler transitions, retention of the normalized state for the next reply, and
derived intermediate-state/fuel costs. A checked control also showed why a bound
restricted to allowed responses cannot simply truncate excluded typed branches
while claiming equality of the entire source tree. This refutes that shortcut,
not handler substitution. `SubstitutionCandidate.lean` records a fully typed
candidate proposition and explicitly does **not** prove its sufficiency.

The isolated experiment used VCVio `25f26bfee60d6700644eb1a69f091091948f15da`
and PolyFun `2348446013d72990237232444e656955f85f97c9`. Root pins remained VCVio
`6d5c7d502ad97f676293a84c3d364c518cbde117` and PolyFun
`c0c923693fc827a41d17116579a0c16ed4873b19`. Local evidence is under
`tmp/handler-substitution-2026-09-15/`: `Scratch/SubstitutionCandidate.lean`,
`Scratch/SubstitutionRestriction.lean`, `logs/substitution-final3.log`,
`logs/audit-result.json`, and `logs/preservation.json`. These local logs are not
promised as files in a fresh clone; the durable measurement record below preserves
the pin and budget metadata.

## Reproducible size and time measurements

The [snapshot JSON](evidence/helios-development-snapshot-2026-09-15.json) records
exact commits, pins, counts, methods, and content-manifest hashes. Physical lines
include blank lines, comments, controls, and audit declarations. These are directory
footprints, not minimum proof sizes, novel mathematics, or developer effort.
Dependencies, scripts, documentation, and sibling umbrella modules are excluded.

| Snapshot and directory | Lean files | Physical lines | Qualification |
| --- | ---: | ---: | --- |
| Symbolic at `a04c7cbbd7c518d0df0ff2932007d98d46e5a5ac` | 861 | 87,550 | Includes 12,318 lines in `Audit.lean`; 75,232 excluding that file. |
| Computational at finite-reduction publication `d428fbd08dd6412702e818c64aafdadee57bf8a0` | 277 | 38,923 | Whole directory, including support and controls; not a theorem dependency slice. |
| Computational at `a04c7cbbd7c518d0df0ff2932007d98d46e5a5ac` | 568 | 79,687 | Published through the native round-trip experiment. |
| Computational working snapshot, 2026-09-15 14:24:41 UTC | 582 | 82,060 | Includes the then-unpublished compositional, efficiency, and coverage files. |

The current-path commit history spans 2026-09-10 12:43:51 to
2026-09-14 05:32:05 UTC for the symbolic directory, and 2026-09-14 05:32:05 to
2026-09-15 10:02:39 UTC for the computational directory, through `a04c7cb`.
These are earliest/latest **committer timestamps for these paths**, without
following renames. They do not measure active work, concurrent agent time, proof
completion time, or the development's full history. The scratch `selected-pin.txt`
records a scheduled window of 11:55:23–13:25:23 UTC on 2026-09-15: a 90-minute
budget, not a measured duration. No verified active-work duration or comparable
Fable measurement is available in this account.

For example, reproduce a committed directory's physical-line count with:

```python
import subprocess
rev = "a04c7cbbd7c518d0df0ff2932007d98d46e5a5ac"
root = "ExplainableCrypto/Helios/Computational/"
paths = subprocess.check_output(
    ["git", "ls-tree", "-r", "--name-only", rev], text=True).splitlines()
paths = sorted(p for p in paths if p.startswith(root) and p.endswith(".lean"))
lines = sum(len(subprocess.check_output(
    ["git", "show", rev + ":" + p]).splitlines()) for p in paths)
print(len(paths), lines)
```

The practical lesson is to test the whole theorem interface early: source law,
observations, encoded inputs, reachable-state coverage, and the provenance of
runtime bounds. Small independent controls can reject an invalid shortcut before
a general proof is attempted. Counting local components or lines cannot establish
that those interfaces compose, or predict the work left to do.
