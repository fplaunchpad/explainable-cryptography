# Continue on another machine

The main library is `ExplainableCrypto`, pinned to Lean and Mathlib 4.32.0.
The current checked increment is the confluence framework plus the homomorphic
three-ciphertext overlap. Full local confluence and ballot secrecy remain open.
The agreed order remains historical symbolic analysis with the documented
tuple correction, followed by a concrete cryptographic repair.

## Restore the workspace

With Git, Lean's `elan` manager, Python 3 and curl available:

```sh
git clone https://github.com/kayceesrk/explainable-cryptography.git
cd explainable-cryptography
git submodule update --init
python3 scripts/fetch_references.py
lake exe cache get
lake build
```

For an existing clone, pull `main` and run the same submodule, reference and Lake
commands. `git submodule update --init` fetches the pinned research libraries. Nested optional native backends are unnecessary for the
main build. The upstream libraries have different Lean versions and are not
Lake dependencies of `ExplainableCrypto`.

The reference downloader retrieves the three exact Helios papers recorded in
[reference-papers.json](reference-papers.json). It verifies SHA-256 before writing
and refuses to replace an existing mismatched file. All three remote downloads
were checked against these hashes during handoff. Use
`python3 scripts/fetch_references.py --check` for an offline verification.
Other local material in `_references/`, build caches, and generated files in
`tmp/` or `output/` are ignored and are not transferred by Git. They are not
needed to build the formalisation. Paper text can be re-extracted with Poppler's
`pdftotext -layout` if useful.

## Resume the research

Read [AGENTS.md](../../AGENTS.md), the [workflow](workflow.md), and the canonical
[task list](../../task%20list.md). Continue at the first open item in section 3.
The confluence results require careful interpretation:

- `triple_peak_joined` is unconditional for arbitrary terms under one common key.
- `confluence_of_local_confluence` and the normal-form characterisations still
  require `LocalConfluentModulo V`; the whole-theory premise is unproved.
- `rootReduce` is complete for raw root rules. Its failed-match result does not
  establish irreducibility modulo E0 or under contexts.
- [The tuple-termination correction](helios-symbolic-tuple-guard.md) is authorised
  and implemented. Keep its literal-source counterexample in the audit.

See the [confluence record](helios-confluence.md) for the current declarations,
test scope and remaining overlap analysis. Do not start the computational-library
phase by treating the conditional symbolic results as a completed privacy proof.

## Validation at handoff

`lake build` passes (3287 jobs), including the finite attack campaigns, rewriting
campaigns and new confluence campaign. Public theorem types and axioms are
printed by `ExplainableCrypto/Helios/Symbolic/Audit.lean`. No custom axioms,
`sorryAx`, warnings or errors were reported in the final build.
