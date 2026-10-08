# Full Named body interpretation

Current internal frontier: [exact conditional location and arbitrary non-check
matching](helios-source-conditional-location.md) are now proved. Check-phase
truth correspondence, required target invariants and final secrecy remain open.
Earlier internal-boundary statements below describe their checkpoint.

Current internal frontier: [general Named communication and actual election
matching](helios-source-communication.md) are now checked without injectivity.
Arbitrary Named conditional correspondence, required target presentation/relation
invariants and final secrecy remain open. Earlier open internal statements below
describe their checkpoint; B9/B10 are still incomplete.

Status: **machine-checked** structural interpretation increment within B9.
B9/B10 remain incomplete; milestone coverage is 8/10 (80%, unweighted).

`Named.Interprets a rho env p` retains a complete evaluated body `p` together
with every active-frame equation. `NameAssignment` maps a sorted `SourceName`
to a natural number. Base and channel names with the same numeral are distinct
keys. A name restriction existentially updates its key; a variable restriction
existentially extends the ground environment. Parallel components share both
assignments and their bodies combine modulo `Agent.EvalEq`.

The definition admits colliding assignments. It is proof instrumentation, not
a new action semantics or a freshness certificate. The existing source rules,
full E/E0, structured-key E5, full-ciphertext E6 and four-field SPK terms are
unchanged. Public observations remain the existing full-E recipe equalities.

## Checked interfaces

- [SourceNameAssignments](../../ExplainableCrypto/Helios/Symbolic/SourceNameAssignments.lean)
  supplies sorted assignment components, permutation/update commutation, and
  support-dependent agreement for formulas, full agents and extended processes.
- [SourceNamedBodyInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceNamedBodyInterpretation.lean)
  defines `Interprets` and proves body equivalence, free-name agreement, unused
  updates, variable renaming and source name-permutation laws.
- [SourceBodyInterpretationContexts](../../ExplainableCrypto/Helios/Symbolic/SourceBodyInterpretationContexts.lean)
  handles parallel zero/association/commutation, variable/name extrusion,
  restriction commutation and both sorts of alpha conversion.
- [SourceNamedStructuralInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceNamedStructuralInterpretation.lean)
  proves `Named.Structural.interprets` for every current constructor. Its
  embedded case uses the existing full Extended structural interpretation;
  hence both active Subst cases and full-E rewriting are included.
- [SourceCanonicalBodyInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalBodyInterpretation.lean)
  characterizes a restriction prefix by assignments fixing every unbound name.
  `restrictedState_interprets_iff` retains pointwise full-E frame values and
  `Agent.EvalEq` of the complete body under the same assignment. Its base and
  channel components fix names outside their respective policies.
  `restrictedState_interprets` supplies the literal frame/body witness.
  `Structural.canonical_interprets` and `canonical_prenex_interprets` carry it
  along an actual structural derivation to arbitrary raw/prenex representatives.

The last interface guarantees an assignment and its exact fixed-name condition.
It does not guarantee injectivity or freshness of the assigned private values.
A fresh, distinct syntactic prefix alone does not strengthen that conclusion.

## Controls and semantics boundary

[SourceNamedBodySPOT](../../ExplainableCrypto/Helios/Symbolic/SourceNamedBodySPOT.lean)
contains nineteen public controls. Independent literal fixtures cover separate
name sorts; one alpha path that moves both frame and output; preservation of
the original environment/body at the renamed binder; rejection of a stale
environment at a free definition; the full SPK fourth field in frame and output;
and a local variable beneath a future input without capture. Canonical election
instances quantify over all ground candidate substitutions, phases, voter
counts and swaps. These interpretation instances require no reachability claim.
Fresh prenex representatives retain the complete body and a single assignment.

The negative controls are operationally significant. Distinct names 40 and 41
satisfy a disequality guard; the constant-zero base map falsifies it and changes
the enabled branch. Output on channel 8 cannot communicate directly with input
on channel 10; the constant-zero channel map creates a core communication.
The full interpretation intentionally admits that collapsed body. Consequently
an arbitrary interpretation witness cannot establish source action matching.

The gate is structural induction plus directed kernel controls. No new randomized
cryptographic campaign is claimed. Previously retained experiments may replay
in the integrated build. Cortier–Smyth Figures 2–4 and the existing source rules
supply the independent semantics reference; interpretation adds no cryptographic
operation or protocol transition.

## Evidence and remaining obligations

Integrated verification: `lake build` passes **3979 jobs**. The log reports
**3899** nonempty standard-only and **74** axiom-free results. The claim audit
covers **2987** public theorem entries and **111** current-status documents.
All eight changed Lean sources have current oleans; **1420** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **44** theorem audits,
including **19** public kernel controls, and checks five assignment/interpretation
definitions. The targeted control build passes **1313 jobs**.
Build log: `tmp/variable-overlap/source-named-body-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-named-body-verification.txt`.

[Independent frame compatibility](helios-source-frame-compatibility.md) and
Named static transitivity are complete. General Named internal correspondence,
required new-frame presentation/relation invariants and final source weak labelled
bisimilarity/symbolic secrecy remain open. Forward Named visible interpretation
is now proved by the subsequent increment described below. Keep the full goal open. Follow
the [proof blueprint](helios-proof-blueprint.md), [results ledger](helios-results.md)
and the existing B9/B10 item in [task list.md](../../task%20list.md).

[Full Named visible interpretation](helios-source-named-visible.md) now supplies
the previously separate canonical-to-prenex visible connection for every actual
free/bound action, retaining full target interpretation. Finite-support
faithfulness is sufficient for Extended internal transport, but fixed old
environment injectivity is refuted by an alpha/dead-field control. General Named
internal correspondence, required new-frame presentation/relation invariants
and final source bisimilarity/secrecy remain open.
