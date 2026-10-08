# Explainable Cryptography

A Lean library for explaining cryptographic specifications, constructions, and
protocol attacks through machine-checked examples. Read the
[demo guide](docs/demos.md) for the existing checked examples.

This is research software. The checked results cover the models and assumptions
recorded in the research notes. The complete historical Helios ballot-secrecy
theorem and a concrete cryptographic repair remain open.
For another machine, follow the [research handoff](docs/research/handoff.md).
See the [prioritised task list](task%20list.md) for immediate next steps.

## Repository layout

| Path | Contents |
| --- | --- |
| `ExplainableCrypto.lean` | Entry point for the formalisation |
| `ExplainableCrypto/MutationTesting.lean` | Elementary specification and construction mutations |
| `ExplainableCrypto/OneTimePad/MutationTesting.lean` | Perfect secrecy, construction mutations, and key-reuse attack |
| `ExplainableCrypto/OneTimePad/Visuals.lean` | ProofWidgets tables connected to the formal probabilities |
| `ExplainableCrypto/Helios/` | Finite replay/permutation counterexamples, controls and axiom audit |
| `docs/` | Proof guide, extension ideas, and library research |
| `task list.md` | Canonical prioritised development backlog |
| `external/` | Pinned upstream source submodules for comparison |
| `_references/` | Local papers, downloaded research materials, and notes; ignored by Git |
| `output/` | Generated documents; ignored by Git |
| `tmp/` | Intermediate build and rendering files; ignored by Git |

## Build and explore

With Lean's `elan` toolchain manager installed, run from the repository root:

```sh
lake exe cache get
lake build
```

The repository pins Lean and Mathlib 4.32.0. `lake build` builds `ExplainableCrypto`, including
the proofs and visualisations. To build one module:

```sh
lake build ExplainableCrypto.OneTimePad.MutationTesting
```

Open `ExplainableCrypto/OneTimePad/Visuals.lean` in VS Code with the Lean extension and place
the cursor on a `#html` command to inspect its table in the InfoView.

## Research and upstream libraries

The agreed next phase is the [historical symbolic Helios theorem](docs/research/helios-symbolic.md),
followed by the concrete cryptographic repair.

- [Checked Helios experiments](docs/research/helios-results.md)
- [Symbolic rewriting results](docs/research/helios-rewriting.md)
- [Helios model and scope](docs/research/helios-model.md)
- [Open repair-target decision](docs/research/helios-repair-ambiguity.md)

- [Helios library analysis](docs/research/helios-library-analysis.md)
- [Library revisions and initial assessment](docs/research/lean-security-libraries.md)
- [Mutation automation ideas](docs/mutation-testing-ideas.md)
- [Formal research workflow](docs/research/workflow.md)

The libraries in `external/` are reference source checkouts, not dependencies of
the `ExplainableCrypto` build. See [external/README.md](external/README.md) for checkout and
update instructions. Each upstream library has its own Lean toolchain.

## License

Original project code and documentation are licensed under the [MIT License](LICENSE).
Copyright (c) 2026 KC Sivaramakrishnan, IIT Madras.

Third-party dependencies and the reference submodules in `external/` retain their
own licenses; the root MIT license does not apply to them. See
[upstream licenses](external/README.md#licenses).
