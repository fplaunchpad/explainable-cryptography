# Explainable Cryptography

A Lean library for explaining cryptographic specifications, constructions and
protocol attacks through machine-checked examples. Read the
[demo guide](docs/demos.md) for the examples.
The [annotated paper index](references.md) links the downloaded papers and explains
their relevance to the project.

Start with the [mathematical reference](docs/formal-reference/main.pdf) for
the Helios protocol, games, attacks, repairs and secrecy theorems. The separate
[historical development catalogue](docs/formal-reference/catalogue.pdf) preserves
supporting component constructions and execution evidence.
The [task list](task%20list.md) is the sole development backlog;
the [blueprint](docs/research/helios-proof-blueprint.md),
[results ledger](docs/research/helios-results.md) and
[handoff](docs/research/handoff.md) record checked progress and remaining obligations.

## Current status

The historical symbolic Helios ballot-secrecy proof is **complete (B1–B10)**.
`scopedVoterElection_ballot_secrecy` establishes source-level weak labelled
bisimilarity for the documented repaired protocol, with the tuple-tail correction
and explicit freshness conditions. Independent attacks, failed repairs and
counterexamples are retained. The [symbolic reuse retrospective](docs/research/helios-reuse-retrospective.md)
is complete. This symbolic result does not establish computational secrecy.

Computational work has **3/3 proof milestones complete under the revised boundary;
publication package complete**. The checked endpoint is
[`ElectionSecurityFamily.Family.ballot_secrecy`](ExplainableCrypto/Helios/Computational/ElectionSecurityFamily.lean).
It proves negligible bias in the original fixed three-voter, two-candidate,
one-honest-trustee game for the encoded attacker interface `Family`.

| Result | Checked scope |
| --- | --- |
| Concrete attack | Smyth's neutral-ciphertext/proof-reuse attack with group algorithms in a probabilistic election game. |
| Concrete repair | The known attack is rejected; honest validation and tally correctness hold under the documented conditions. |
| Finite reduction | Original prepared-election bias is bounded by two exact DDH advantages and explicit rejection, simulation, extraction and sampling losses. |
| Attacker coverage | Actual serialized input bounds and query clocking derive a `PreparedFamily`; complete source/game equality and final-cache equality preserve the original bias. |
| Computational secrecy | `Family.ballot_secrecy` derives negligible original bias from negligible inverse field size, two named efficiency hypotheses for the exact normalized reductions, and DDH for the same fair-coin machine class and group encoding. |

The **revised boundary** retains explicit external mathematical arguments:
uniformly polynomial-clocked strict oracle-PPT implementations satisfy the
`Family` query and encoded output-size conditions, and the two exact reductions
have polynomial-time finite fair-coin implementations. Lean checks the encoded
reduction and coverage theorems; it does not prove those implementation arguments
or a characterization of standard PPT. `Family` also carries representation,
parameter, fingerprint, generator and private encoding conditions. The
[closing audit](docs/research/helios-computational-closing-audit.md) lists every
condition, the four theorem hypotheses and the evidence supporting each external
argument. It retains the distinction between all typed reply paths and runs
against consistent random oracles. The kernel axiom audit checks proof dependencies,
not these external arguments or the modelling choices.

These are **two checked secrecy results for separately scoped models of the same
historical protocol**. No symbolic/computational correspondence has been proved.
The [scope comparison](docs/research/helios-scope-comparison.md) records differences
in repair, observation timing, rejection, freshness and cryptographic semantics.

C5–C8's stronger machine-efficiency construction is **deferred**, with checked
TM modules and controls preserved in the optional `HeliosExecution` target.
This stronger construction is outside the revised case-study deliverable.
Machine definitions required by the named efficiency hypotheses stay in the
default build. Historical attack transport is a separate validation
item; a transfer framework and broader election models remain future research.
The [experience report](docs/research/helios-development-experience.md) records
measured development artifacts and pinned-library findings without treating them
as general complexity or impossibility results. Historical component increments
remain in the [results ledger](docs/research/helios-results.md).

The staged [election-framework research question](docs/research/election-computational-soundness-idea.md)
now includes ballot privacy, receipt-freeness and end-to-end verifiability over a
shared Lean semantics, with BeleniosRF and SeleneRF as candidate case studies.
Implementation has not started; computational transfer remains a later question.

## Build and audit

The root project pins **Lean/Mathlib 4.33.1** and
[VCVio](https://github.com/Verified-zkEVM/VCVio) revision
`6d5c7d502ad97f676293a84c3d364c518cbde117`. All usable symbolic and computational
code shares this toolchain and root Lake project. The default `ExplainableCrypto`
target contains the symbolic development and retained computational case study.

With Lean's `elan` toolchain manager installed, run:

```sh
lake exe cache get
lake build
python3 scripts/audit-helios-computational.py
python3 scripts/check_helios_targets.py
python3 scripts/check_helios_claims.py
```

The [explicit retained roots](ExplainableCrypto/Helios/Computational.lean) include
secrecy, the concrete attack, repair/correctness and their independent controls.
The [source guide](ExplainableCrypto/Helios/Computational/README.md#build-targets)
explains the selection. The import checker compares their closure with the actual
Lean environment loaded by the default target.

Build and audit **all** computational evidence, including the deferred execution
work, explicitly:

```sh
lake build HeliosExecution
python3 scripts/audit-helios-computational.py --scope full
python3 scripts/check_helios_targets.py --full
```

Existing module paths and theorem names are unchanged. Historical native gates
remain available in the optional CI job and the source guide; build the optional
target before running those gates. No build-time saving is claimed from the split.

Build the PDFs separately:

```sh
bash scripts/build-formal-reference.sh --document reference
bash scripts/build-formal-reference.sh --document catalogue
```

The reference uses only the default build; the catalogue builds `HeliosExecution`.
Both commands check citations, typed statements, links and layout diagnostics.
The PDF builds require Tectonic and Poppler; see the
[formal-reference instructions](docs/formal-reference/README.md).
To check one module, for example:

```sh
lake build ExplainableCrypto.Helios.Computational.SamplerOperandsControls
python3 scripts/check-helios-prepared-scalar.py
```

Open `ExplainableCrypto/OneTimePad/Visuals.lean` in VS Code with the Lean extension
and place the cursor on a `#html` command to inspect the demonstration tables.

## Repository layout

| Path | Contents |
| --- | --- |
| `ExplainableCrypto.lean` | Main formalization entry point |
| `ExplainableCrypto/MutationTesting.lean` | Elementary specification and construction mutations |
| `ExplainableCrypto/OneTimePad/` | Perfect secrecy, mutations, key-reuse attack and visualizations |
| `ExplainableCrypto/Helios/Symbolic/` | Completed historical symbolic proof and controls |
| `ExplainableCrypto/Helios/Computational.lean` | Explicit retained computational roots for the default build |
| `ExplainableCrypto/Helios/Execution.lean` | Optional full computational aggregate (`HeliosExecution`) |
| `ExplainableCrypto/Helios/Computational/` | Unmoved source files for both targets |
| `docs/formal-reference/` | Mathematical reference and historical catalogue PDFs, LaTeX, typed checks and claim ledger |
| `docs/research/` | Research evidence, model boundaries and dependency blueprint |
| `task list.md` | Canonical development backlog |
| `external/` | Pinned reference checkouts; separate from Lake's dependencies |
| `_references/`, `tmp/`, `output/` | Ignored local research and generated artifacts |

## Research workflow

[AGENTS.md](AGENTS.md) and the [research workflow](docs/research/workflow.md) require
independent controls, explicit assumptions and evidence-accurate documentation.
Substantial integrated/audited increments are committed and pushed with the
synchronized README and PDF. Supporting lemmas are batched into completed
obligations; intermediate proof attempts and routine logs remain local.

See the [computational model](docs/research/helios-computational-model.md),
[computational source guide](ExplainableCrypto/Helios/Computational/README.md),
[library validation](docs/research/computational-probes/README.md),
[repair analysis](docs/research/helios-repair-ambiguity.md) and
[upstream checkout instructions](external/README.md).
Reference projects retain their own pins and toolchains. The root build uses
Mathlib and VCVio as direct external Lean dependencies; the other reference
submodules are not Lake dependencies.

## Continuous integration

[Check development](https://github.com/fplaunchpad/explainable-cryptography/actions/workflows/check.yml)
runs on pushes to `main`, pull requests and manual dispatch. The ordinary
`case-study` job builds the default target, verifies the actual retained import
closure, audits its computational theorems and symbolic claims, builds/checks
the mathematical reference, and runs selected independent attack, repair and
reduction fixtures.

Manual dispatch with **`deferred: true`** additionally builds/audits the full
computational target, runs the preserved native execution gates and complete
independent fixture campaign, and builds/checks the historical catalogue.
Routine CI does not invoke those deferred jobs or the catalogue builder.
Audit logs are uploaded as artifacts. New main-branch pushes do not cancel earlier
main-branch runs; stale pull-request runs are cancelled. Local checks and hosted
CI results are separate evidence; current hosted results are at the workflow link.

## License

Original project code and documentation are licensed under the [MIT License](LICENSE).
Copyright (c) 2026 KC Sivaramakrishnan, IIT Madras.

Third-party dependencies and reference submodules retain their own licenses;
the root MIT license does not apply to them. See [external/README.md](external/README.md).

## Public repository provenance

The public repository starts with fresh history. The current research snapshot
was imported from the predecessor's main revision `db1c1c5`; historical commit IDs
and test records in the research notes refer to that earlier development. The
proposal and private research-skills checkout are not part of this repository.
