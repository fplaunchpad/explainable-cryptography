# Formal research workflow

Use [task list.md](../../task%20list.md) as the single development backlog.
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
