# Process and symbolic library exploration

Snapshot: 2026-09-12. This records the initial source-only exploration.
The subsequent [completed retrospective](helios-reuse-retrospective.md) supplies
selected upstream builds, checked adapters and quantified costs after B1–B10.
The proposals and unperformed-check statements below describe this earlier
exploration, not the current verification status. Upstream pins are unchanged.

## Pins and scope

| Reference | Revision | Toolchain / scope |
| --- | --- | --- |
| [CSLib](../../external/CSLib) | `b777e0891698a7764e1387300eb0f9053b417b42` | Lean 4.34.0-rc2 |
| [SymbolicCryptographyLean](../../external/SymbolicCryptographyLean) | `607cf34d3c85268c8ed2e923424078fce138399d` | Lean 4.20.0-rc5 |
| [Isabelle-AFP](../../external/Isabelle-AFP) | `101a3a4705e36063419d68fe6631b986aabcdeaa` | Development AFP Git mirror; sparse `Psi_Calculi`, `Pi_Calculus`, entry metadata |
| [LeanDY](../../external/LeanDY) | `e0705986c5dea547848bf80c10b5c4f88ae6868c` | Existing Lean 4.24.0-rc1 pin, preserved |

CSLib and SymbolicCryptographyLean are new Git submodules. Psi-calculi lives
inside AFP, whose canonical upstream uses Mercurial; the submodule uses the
[Git mirror](https://github.com/isabelle-prover/mirror-afp-devel).
The AFP revision is a development snapshot, not a claim of compatibility with
an installed Isabelle release. `Psi_Calculi/ROOT` uses `HOL-Nominal` as parent.
VCVio and CatCrypt-core pins were also preserved.
These reference checkouts do not add Lake dependencies to the main project.

## CSLib: reusable transition-system theory

Inspected [Bisimulation.lean](../../external/CSLib/Cslib/Foundations/Semantics/LTS/Bisimulation.lean),
its LTS/HasTau support and the CCS behavioural example.

- `IsBisimulation` relates two potentially different state types and requires
  both directions of labelled matching with related successors.
- `IsBisimulation.comp` and `Bisimilarity.trans` provide composition.
- `IsWeakBisimulation` uses saturated transition systems.
  `IsSWBisimulation` expresses single-step challenges with weak matching;
  `WeakBisimilarity.weakBisim_eq_swBisim` connects the formulations.
- `IsBisimulation.traceEq` supplies a trace-equivalence consequence. The file
  also retains examples distinguishing trace equivalence from bisimulation.

Candidate reuse: generic B10 relation composition, weak-step reasoning and
connections to trace properties. Instantiate the existing LTS interface instead
of duplicating its generic theory, if a checked adapter preserves our target.

Boundary: these definitions alone do not require cryptographic static
equivalence of public frames. An adapter must retain that obligation, bound
output freshness, exported handle domains and the historical action semantics.
They do not construct the source correspondence currently needed in B9.
The [Languages README](../../external/CSLib/Cslib/Languages/README.md) explicitly
lists general binder facilities and representation connections as unfinished
work. Context/substitution interfaces should not be mistaken for a complete
applied-pi implementation. Toolchain alignment needs an isolated prototype.

## SymbolicCryptographyLean: expression security and computational soundness

Companion paper: Dziembowski, Fabiański, Micciancio and Stefański,
[*Computationally-Sound Symbolic Cryptography in Lean*](../../_references/dziembowski-fabianski-micciancio-stefanski-2025-symbolic-cryptography-lean.pdf),
[ePrint 2025/1700](https://eprint.iacr.org/2025/1700), downloaded 2026-09-12.
Its §1 explicitly identifies the pinned repository as the implementation.
Sections 2–4 describe expression indistinguishability, circuit garbling and
the computational interpretation/soundness bridge. Section 5 lists expression
language extensions and a concrete polynomial-time definition as future work.
The paper's polynomial-time abstraction agrees with the explicit predicate,
closure and reduction-efficiency premises in the source theorem below.

Inspected [Expression/Defs.lean](../../external/SymbolicCryptographyLean/SymbolicGarbledCircuitsInLean/Expression/Defs.lean),
the documented normalization/adversary-view organization, and the public
[soundness theorem](../../external/SymbolicCryptographyLean/SymbolicGarbledCircuitsInLean/Expression/ComputationalSemantics/Soundness.lean).

The expression language contains bits, keys, pairs, conditional swaps,
encryption and hidden encrypted values. Its structure differs from our
homomorphic ciphertext and proof-term algebra; it is not an input/output
process language with applied-pi active substitutions.

`symbolicToSemanticIndistinguishability` assumes an adversary complexity
predicate, closure under composition, polynomial-time membership of the
specified reductions, IND-CPA security, and symbolic indistinguishability of
the two expressions. The conclusion is computational indistinguishability of
their interpreted distributions. These premises must accompany any reuse claim.

Candidate reuse: architecture for symbolic views, semantics-preserving
normalization/renaming, and an eventual computational bridge for a compatible
fragment. It does not establish computational soundness for our homomorphic
equations or complete source protocol. Its bundled `VCVio2` is a modified
fragment, not our separately pinned VCVio checkout. Avoid conflating their APIs.

## Isabelle Psi-calculi: the closest binder/frame design precedent

Inspected [Frame.thy](../../external/Isabelle-AFP/thys/Psi_Calculi/Frame.thy),
[Weak_Bisimulation.thy](../../external/Isabelle-AFP/thys/Psi_Calculi/Weak_Bisimulation.thy),
Agent/Semantics and the session ROOT. The adjacent Pi_Calculus session is
available as a reference but has not received a declaration-level audit here.

Frames use nominal assertions and restricted names; `frameResChain` packages
restriction sequences and `frameChainAlpha` provides renaming under explicit
freshness/permutation premises. Weak bisimulation is coinductive in the `env`
locale and includes weak static implication, weak simulation, extension of the
assertion environment and symmetry. This is materially richer than a bare LTS
matching relation.

Candidate reuse: binding-sequence representation, custom induction/inversion
rules, freshness bookkeeping, and organization of static/dynamic proof
obligations. This is a design or theorem-port candidate, not a Lean import.
An instance must establish the locale laws and relate Psi assertions, frames
and semantics to the historical applied-pi model. Expressiveness alone does
not prove that this translation preserves our secrecy statement.

## LeanDY: existing trace-security infrastructure

Rechecked [Attacker.lean](../../external/LeanDY/Leandy/Lib/Attacker.lean).
`Attacker.AttackerKnows` includes published/initial knowledge and constructor/
destructor closure. `Attacker.attacker_sound` assumes `valid_trace` and concludes
that every derivable message is public under its labeling discipline.

Candidate reuse: protocol DSL, trace invariants, typing and attacker-proof
automation. This statement does not by itself prove two-world static
equivalence or ballot secrecy. Extending its message algebra for homomorphic
operations would require checking the associated metatheory. See the existing
[library analysis](helios-library-analysis.md) for the earlier comparison.

## What the post-B audit must establish

The user wants to know how much completed work could have reused existing
developments. A source match is only a candidate. The audit should map our
modules and public theorem dependencies to exact upstream declarations,
distinguishing direct imports, small checked adapters, substantial extensions,
cross-prover ports and unmatched obligations. Representative prototypes must
retain the completed secrecy theorem's hypotheses and observations.

Report gross overlap and net replacement after adapters separately. Count
implementation/proof sources, controls, audit scaffolding and comments
separately, and avoid double-counting shared dependencies. Distinguish
demonstrated replacement from estimated avoidable work; do not infer elapsed
time saved from line counts. Record whether the relevant upstream revision was
available when our work started. Task acceptance and ordering live only in
`task list.md`.

## Verification performed for this exploration

Verified the new Git registrations/pins and inspected the named source
interfaces. No upstream source was edited. No upstream build, runtime benchmark,
transitive proof-axiom audit or semantics adapter was executed. No new security
theorem is claimed. Reference links and parent documentation whitespace are
checked separately from the running main proof development.
