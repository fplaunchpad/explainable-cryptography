# Project instructions

- `task list.md` is the only development task list. Update it alongside evidence
  when completing work. `docs/mutation-testing-ideas.md` is exploratory context.
- Include completed/total main milestones and the active milestone in progress
  updates, using the stages in `task list.md`. Report supporting prerequisites
  separately; milestone counts are not percentages of effort or time remaining.
- After each substantial, integrated and audited research increment, commit and
  push the coherent changes, including synchronized documentation and the PDF.
  Do not wait for the entire goal or ask again for routine publication. Do not
  publish unfinished experiments or unrelated user changes; preserve upstream pins.
- Batch research synchronization around completed proof obligations and coherent
  publication increments, not supporting lemmas. During a bounded probe use
  targeted checks and local logs; record consequential counterexamples promptly.
  Synchronize durable documents/PDF and run complete audits once per publication
  increment. Explicit goal deliverables still apply.
- Before every push, read `README.md` and reconcile its status, theorem coverage,
  active work, build instructions and navigation links with the checked source,
  `task list.md` and results ledger. Fix stale claims before pushing; do not
  require a README edit when the existing text is still accurate.
- Keep `docs/research/helios-proof-blueprint.md` current as the symbolic proof
  dependency map, not a second backlog. Read it before Helios symbolic research;
  update the current milestone, operator frontier, evidence and completion count
  alongside `task list.md` and the results ledger after each research increment.
  Report the current blueprint position when summarising proof progress, and
  distinguish milestone coverage from effort remaining.
- Read `docs/research/workflow.md` before formal research. Record falsifiable
  claims, independent controls, assumptions and reproducible evidence. Audit
  research prose against the public statements of the formal artifacts.
- Build the main project with `lake build`. Its Lean dependencies are managed
  by Lake; the reference submodules are not part of this build.
- Keep usable project Lean code under `ExplainableCrypto` in the root Lake
  build and on one toolchain, including computational proofs. Native upstream
  comparison probes may use their pinned toolchains; preserve those checkouts.
- For substantive formal changes, retain independently derived positive and
  negative controls, record assumptions and use the research workflow's evidence
  labels. No search failure counts as evidence of security.
- Keep public observations explicit in cryptographic models. Never claim a
  full protocol privacy proof from a blocked attack or equal tallies alone.
- Preserve upstream checkouts and pinned revisions unless updating them is part
  of the task. Each upstream project has its own build and instructions.
- `_references/`, `tmp/`, and `output/` hold local or generated materials.
  Durable project documentation belongs in `docs/`.
