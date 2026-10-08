# Helios mathematical reference and historical catalogue

Read the [mathematical reference](main.pdf) for the protocol and public
observations, symbolic secrecy, concrete attack and repair, computational game,
mathematical bias and secrecy theorem, assumptions and model comparison.
The exact Lean attacker interface and theorem statement are in an appendix.
Common applied-pi and symbolic homomorphic foundations are presented through
their verified library interfaces.

The [historical development catalogue](catalogue.pdf) preserves supporting
cryptographic and execution components. Each subsection and running page header
identifies its historical role. Obsolete status assertions have been removed;
local interface limitations remain explicit. Its source provenance is
`9273cdc` (recorded before the public-history migration).
It does not establish complete machine implementations of the reductions.

The computational theorem retains every `Family` condition and all four theorem
hypotheses. The reference explains the accuracy degree, the finite reduction,
and the external direction from the chosen finite machine convention to
conventional strict PPT and same-encoding DDH. Attacker membership and exact
reduction efficiency remain external arguments. The two Helios models differ
in repair, observations and rejection; no correspondence is proved.

## Build and check each document

Use the pinned Lean toolchain, Tectonic (or XeLaTeX with `fvextra` and `fontspec`),
Poppler, and DejaVu Sans Mono (Menlo on macOS).

```sh
# Default: mathematical reference, retained case-study dependencies only
bash scripts/build-formal-reference.sh --document reference

# Historical catalogue, including the optional execution development
bash scripts/build-formal-reference.sh --document catalogue
```

The first command runs `lake build`; the second runs `lake build HeliosExecution`.
Each checks its own declaration anchors, local links/references, typed statement
concordance, document-gate fault tests, PDF compilation and extracted text.
The reference additionally checks verbatim source snippets and rejects any
citation or statement dependency that reaches deferred computational modules.
Logs are separated under `tmp/formal-reference/reference/` and `catalogue/`.
Default CI builds the reference. Manual dispatch with `deferred: true` also
builds the catalogue and runs the preserved execution gates.

For already built Lean modules, run only the evidence gate:

```sh
python3 scripts/check-formal-reference.py --document reference
python3 scripts/check-formal-reference.py --document catalogue
```

The complete computational theorem audits remain separate:

```sh
python3 scripts/audit-helios-computational.py
python3 scripts/audit-helios-computational.py --scope full
```

`statements/` holds exact fragments of `ElectionSecurityFamily.lean`; the gate
compares them byte-for-byte with the source. `StatementChecks.lean` restates five
symbolic interfaces and the computational game, bias and full-hypothesis theorem.
`CatalogueStatementChecks.lean` retains four native execution interfaces.
These checks and axiom reports do not establish mathematical prose equivalence,
cryptographic hardness, model adequacy or either external efficiency argument.
The gate rejects changed theorem snippets, missing/malformed anchors, dangling
references, unexpected/missing axiom reports, deferred reference dependencies
and obsolete status vocabulary. The PDF builder rejects overflow, missing glyphs
and unresolved references. Rendered-page review is recorded separately.

## Evidence and navigation

- [Claim ledger](claim-ledger.md): mathematical displays, external arguments and their evidence.
- [Closing audit](../research/helios-computational-closing-audit.md): complete assumptions and implementation arguments.
- [Scope comparison](../research/helios-scope-comparison.md): declaration-backed differences between models.
- [Experience report](../research/helios-development-experience.md): measured snapshots and inspected library interfaces.
- [Blueprint](../research/helios-proof-blueprint.md): proof dependencies.
- [Results ledger](../research/helios-results.md): historical and current checks.
- [Task list](../../task%20list.md): sole development backlog.

Earlier page/section references in historical evidence refer to the PDF at the
cited commit. Current source paths and theorem statements are preserved; the
split changes their exposition and document numbering.
