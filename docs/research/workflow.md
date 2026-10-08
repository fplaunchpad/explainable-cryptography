# Formal research workflow

Use [task list.md](../../task%20list.md) as the single development backlog.
For Helios symbolic research, also read the maintained
[proof blueprint](helios-proof-blueprint.md). It records dependencies and
acceptance conditions, not a separate backlog. After each research increment,
update its current milestone, operator frontier, evidence and completion count
alongside the existing task-list item and results ledger. Separate targeted
checks from integrated build/audit evidence, and report milestone coverage
separately from any estimate of effort remaining. This maintenance requirement
records the user's instruction to keep the proof blueprint up to date.

Before a formal experiment, record its goal, falsifiable candidate claim,
smallest falsifier, formal oracle and independent reality oracle. For Helios,
Cortier–Smyth supplies the historical protocol being modelled; each departure
belongs in the model document. Research plans do not establish current proof coverage. Lean definitions determine what a theorem means, and its public
statement determines what has been checked. Tests validate only their stated
scope; prose must not expand any of these claims.

Use this record in `helios-results.md` when the experiments begin:

```text
Claim:
Status: conjectured | refuted | machine-checked | validated | measured | specified | staged
Formal oracle: declaration and reproducible command
Falsifier:
Positive control:
Negative control:
PBT gate: generator, seeds, sizes, counts, failures and gaveUp
Trusted definitions:
Reality oracle: source section, independent fixture or implementation
Residual assumptions and unsupported cases:
```

For difficult general conjectures, run property-based refutation first. Generate
reachable states, make the harness detect a known defect, retain minimized
failures, and convert decisive examples to checked theorems. Small
Proof-Oriented Tests (SPOTs) pair a positive case with a negative that excludes a
tempting degenerate explanation. Derive expected values independently.

Before marking research complete, build the relevant modules, check the public
theorem and its axioms, run the controls, classify test outcomes, and update the
claim record and task list. If a proof fails, classify whether the problem is
proof engineering, a false claim, vacuity, incorrect semantics, or a missing
constraint. Preserve the original claim's status when proving a weaker result.

The repository reorganisation changed module paths and namespaces without
introducing a new cryptographic claim. Its verification is the successful
`lake build` of the relocated demonstrations; no new Helios proof, property-based
campaign, or upstream-library build is claimed by that check.

## README review before pushing

Before every push, read the root README against the current checked source,
`task list.md`, results ledger and formal reference. Reconcile completed theorem
coverage and limitations, active and deferred work, build/dependency instructions,
and navigation links. Correct stale claims before pushing. An unchanged README
is acceptable when reviewed and accurate; touching the file is not evidence of
freshness. Keep locally checked, integrated/audited and published results distinct.
This is a required pre-push review, not an additional user-approval step.

## Publish substantial checked increments

Commit and push after each substantial integrated/audited increment, rather than
waiting for the full research goal. This records the user's publication preference
of 2026-09-14 and authorizes routine pushes without renewed confirmation.
Before committing, complete the relevant root build, controls, axiom and document
checks; synchronize the task list, blueprint, results ledger, README and formal
reference PDF. Use a commit message that describes the checked result and its
remaining boundary. Include the generated PDF. Exclude local build caches and
unrelated user changes; preserve upstream pins. Verify the pushed commit and
report its link. Intermediate experiments can remain local until integrated;
never imply that a published partial result closes the full secrecy goal.


## Batch synchronization by result

The user requested reduced synchronization overhead on 2026-09-15. Treat a
completed proof obligation as the unit of progress; supporting lemmas and
routine proof-engineering fixes are not separate publication increments.
During a bounded experiment, use targeted checks and short local logs. Record
false claims, counterexamples and changes to trusted definitions promptly.
At obligation closure, update the existing task-list item and add one compact
result record containing the theorem interface, assumptions, controls, commands
and remaining boundary. Keep routine failed elaboration traces in local logs.

At a coherent publication boundary, reconcile the README, blueprint and formal
reference once, run the relevant full build/audits and regenerate/review the PDF
once. Repeat a check only when intervening changes can invalidate it. Supporting
fragments do not each trigger this package. Prefer updating current status in
place to copying long status narratives across documents; the results ledger
holds evidence and other documents summarize and link to it.

Explicit goal acceptance remains binding: the current 90-minute round-trip
experiment includes documentation, PDF, audits and publication. Future bounded
feasibility goals may specify a checked local outcome before a later publication
batch. This changes synchronization cadence, not theorem scope or evidence
standards. Main milestone/checkpoint counts must be accompanied by the exact
remaining path to the top-level theorem; they do not estimate remaining work.
