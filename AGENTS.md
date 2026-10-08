# Project instructions

- `task list.md` is the only development task list. Update it alongside evidence
  when completing work. `docs/mutation-testing-ideas.md` is exploratory context.
- Read `docs/research/workflow.md` before formal research. Record falsifiable
  claims, independent controls, assumptions, and reproducible evidence. Audit
  research prose against the public statements of the formal artifacts.
- Build the main project with `lake build`. Its Lean dependencies are managed
  by Lake; the reference submodules are not part of this build.
- For substantive formal changes, retain independently derived positive and
  negative controls, record assumptions and use the research workflow's evidence
  labels. No search failure counts as evidence of security.
- Keep public observations explicit in cryptographic models. Never claim a
  full protocol privacy proof from a blocked attack or equal tallies alone.
- Preserve upstream checkouts and pinned revisions unless updating them is part
  of the task. Each upstream project has its own build and instructions.
- `_references/`, `tmp/`, and `output/` hold local or generated materials.
  Durable project documentation belongs in `docs/`.
