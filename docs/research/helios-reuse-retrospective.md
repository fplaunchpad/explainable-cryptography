# Retrospective reuse audit of the completed historical proof

Snapshot: 2026-09-12. Status: **measured** inventory and **machine-checked**
representative adapters. B1–B10 were completed before this audit. The frozen
endpoint is [scopedVoterElection_ballot_secrecy](../../ExplainableCrypto/Helios/Symbolic/SourceBallotSecrecy.lean).
It proves source weak labelled bisimilarity for the actual repaired historical
scoped elections, under name/channel freshness and nonce freshness for valid
ground candidate substitutions, with arbitrary finite administration size.
The [blueprint](helios-proof-blueprint.md) records its acceptance evidence.

The experiments demonstrate reuse of generic transition theory and a small
binder lemma. They demonstrate **no positive net source reduction** in the
finished proof. This is a result about the substitutions tested, not a claim
that the whole development was minimal or that a different initial design
could not have saved substantial work. No defensible percentage of avoidable
research effort follows from these measurements.

The proof already uses Lean, Mathlib, Batteries and Aesop. Homomorphic
cryptographic equations and their observation theory were developed here;
general mathematics and proof infrastructure were already reused.

## Frozen dependency and size measurements

The freeze records every transitive project import's SHA-256, the main Lake
manifest, the successful final build log and all reference pins in
`output/reuse-audit/completed-secrecy-snapshot.json`. The entry imports 554
project modules. [DependencySnapshot.lean](reuse-adapters/DependencySnapshot.lean)
walks the checked endpoint's types and proof/definition constants, including
constructor and recursor dependencies. It finds 11,345 distinct constants:
4,694 project constants, 4,666 from Init, 1,875 Mathlib, 109 Batteries and one
Aesop. Dependencies shared by several branches are counted once.

The project constants occur in 475 files. The following are **whole-file
footprints**, not a minimum proof size or a line-level slice of the theorem.
An imported or kernel-used file can contain many unused declarations.
The full inventory also includes exploratory work and retained controls.

| Scope | Files | Code lines | Comment-only lines | Blank lines | Physical lines |
| --- | ---: | ---: | ---: | ---: | ---: |
| All symbolic model/proof files | 583 | 39,572 | 3,572 | 5,275 | 48,419 |
| Control/experiment files | 277 | 21,507 | 1,835 | 3,441 | 26,783 |
| Audit file | 1 | 10,709 | 117 | 1,492 | 12,318 |
| Total symbolic directory | 861 | 71,788 | 5,524 | 10,208 | 87,520 |
| Files defining endpoint kernel dependencies | 475 | 33,369 | 2,993 | 4,401 | 40,763 |
| Transitive project imports | 554 | 38,013 | 3,428 | 4,997 | 46,438 |
| Imported files with no endpoint kernel constant | 79 | 4,644 | 435 | 596 | 5,675 |

The last three rows overlap the first four; **do not add them**. The role
classification uses filenames. Two kernel-used control files, `SPOT` and
`RewriteSPOT`, contain general supporting lemmas, so even the control category
is not wholly removable. The 79 import-only files are a possible import cleanup
scope, not demonstrated redundant research or external-library replacement.

Of the 475 kernel-used files, 201 `Source*` files occupy 12,809 code lines;
the other 274 occupy 20,560. These distinguish process infrastructure from the
remaining symbolic development by filename only. Neither aggregate establishes
that a library can replace those files.

[scripts/reuse-audit/inventory.py](../../scripts/reuse-audit/inventory.py)
reproduces the inventory, strips nested comments for code-line counts, and
checks the frozen source hashes. Outputs are `output/reuse-audit/module-inventory.csv`,
`inventory-summary.json` and `kernel-dependencies.json`.

## Mapping the actual obligations to existing work

The [source exploration](helios-reuse-source-exploration.md) supplies pinned
source links and detailed interface statements. This table distinguishes
checked reuse from candidates requiring new metatheory.

| Completed local obligation | Upstream declaration/interface | Classification and adaptation boundary |
| --- | --- | --- |
| Generic B10 weak-transition relations in `SourceBallotSecrecy` | CSLib `LTS.IsSWBisimulation.isWeakBisimulation`, `LTS.IsWeakBisimulation.comp` | **Checked adapter.** Actual source actions fit the LTS after packaging varying finite handle domains. Full `Named.StaticEq`, closedness and domain conditions still need local evidence. Composition is not used by the completed endpoint. |
| Restricted-frame free names in `SourceUnusedRestrictions` | AFP Psi-calculi `frameResChainFresh` | **Checked cross-prover port.** The Lean port independently proves the exact local free-name equation without importing its original proof. It is slightly longer. |
| Source alpha/frame transport | AFP `frameChainAlpha`, nominal frames and restriction sequences | **Partial port/design precedent.** One-binder structural alpha is checked on the actual source frame. Our `allNames` freshness premise is retained; the nominal permutation/support formulation is not silently substituted. A wholesale replacement needs a representation and semantics translation. |
| Reachable extraction, structural presentation, private policies and successor matching in `SourceElectionRelation` and dependencies | CSLib LTS theory; AFP Psi-calculi semantics/weak bisimulation | **Unmatched by the tested adapters.** They supply general organization, not the historical reachable-state correspondence. The concrete CSLib bridge calls the completed B9 proofs for every action. |
| Full-E recipes, minimum observations and adversarial ballot reconstruction | LeanDY `Attacker.AttackerKnows`, `Attacker.attacker_sound` | **Major extension candidate.** `valid_trace` implies a one-world message-publicness property. Extending its algebra with our homomorphic operations, randomness and SPK equations requires new metatheory and a two-world observation argument. No substitution checked. |
| Symbolic observation equivalence and possible computational interpretation | SymbolicCryptographyLean `symbolicToSemanticIndistinguishability` | **Major extension candidate.** Its expression language and explicit complexity, reduction-efficiency and IND-CPA assumptions differ. Its soundness theorem is not soundness of our equations or historical source protocol. No substitution checked. |
| Symbolic ciphertext equations / future concrete encryption layer | VCVio `elGamal_IND_CPA_le_q_mul_ddh`; CatCrypt-core ElGamal DDH example | **Computational follow-on candidates.** Actual probabilistic group encryption, DDH reductions and their game assumptions do not discharge full-E recipe static equivalence or B9. Group/interface adapters and a protocol reduction would be additional work. |
| Historical homomorphic component-weeding protocol | ProVerif voting-framework paper | **Design comparison only.** The paper explicitly excludes homomorphic tallying; its Helios-like example uses a different protocol construction. It cannot replace the target's repair or secrecy theorem. |

The homomorphic algebra, accepted-ballot reconstruction, public partial
decryptions and rejection-sensitive process correspondence remain necessary
obligations for this target. This does not assert that their current proofs
are the shortest possible proofs. The retained checked counterexample to
“semantic realization equality implies structural presentation” continues to
rule out that attempted shortcut.

## Checked substitutions and their costs

### CSLib: native build and actual source integration

The exact CSLib pin builds its selected bisimulation module and the generic
[CSLibComposition.lean](reuse-adapters/CSLibComposition.lean) experiment under
its native Lean 4.34.0-rc2 and locked Mathlib. `FramedWeak` retains an unchanged
LTS, full observation predicate and equal handle domains. Its composition
proof calls upstream `IsWeakBisimulation.comp`. Independent empty-LTS controls
show that dynamic matching alone permits unequal observations and unequal
domains; the additional clauses reject both cases.

[SourceCSLibBridge.lean](reuse-adapters/SourceCSLibBridge.lean) checks against
the completed proof's Lean 4.32.0 and Mathlib. `Step` wraps exactly original
`Named.Reduction`, scoped `FreeStep` and `BoundOutput`. A bound target retains
all old handles and adds the fresh coordinate using the existing `outputHandle`
bijection. `bound_changes_domain` excludes a same-domain publication.
`Observes` carries actual full `Named.StaticEq`; its transitivity calls the
completed source-frame proof. The matching relation carries the completed
`SourceElectionRelation`, including reachability, executions and presentations.

`actual_scoped_pair_has_cslib_witness` constructs the actual swapped-election
pair under the same name, candidate-nonce and channel freshness assumptions.
`match_step` handles all three original action constructors, deriving partner
label scope from the full exported domain. `source_composition_is_framed`
then applies upstream composition to that source LTS. Thus the adapter does
preserve actual actions, observations and assumptions. It **does not remove
B9**, and it does not establish that the local largest-relation definition and
CSLib's generic definition can be interchanged without the observation wrapper.

The compatibility copy of CSLib needs one changed proof line in an unrelated
TFAE corollary: explicit `lts₁`/`lts₂` arguments and `.out 0 1` instead of
`.out 1 2`. Mathlib's indexing convention differs between the pinned versions.
The corollary's statement and the composition proof are unchanged. This is a
**proof-engineering failure**, resolved in the isolated copy. All upstream
checkouts and the main manifest remain unchanged.

### AFP-inspired binder/frame port

[FramePort.lean](reuse-adapters/FramePort.lean) imports `SourceFrameStructure`,
whose import closure excludes the original `SourceUnusedRestrictions` proof.
`frameResChainFresh` ports the restriction-list freshness equation by induction.
`freeNames_restrictNames_replacement` derives the exact existing local equation.
`frameChainAlphaOne` retains the local stronger all-name freshness requirement
and uses actual source structural alpha and full frame extraction.

The literal full-SPK frame control retains every proof field; a public literal
already present in the frame fails the proposed freshness condition. Another
control distinguishes a restricted name from a public name. These exclude
vacuous name erasure and treating every name as fresh. The port is checked in
Lean 4.32.0. **No Isabelle runtime build or imported Isabelle proof is claimed**:
the development AFP pin does not specify an installed matching Isabelle runtime.
This is a measured cross-prover adaptation, not validation of the entire AFP
locale or its equivalence with our representation.

### Gross candidate scope versus net demonstrated replacement

| Scope, counted once | Original code lines | Adapter code lines | Demonstrated removal |
| --- | ---: | ---: | --- |
| Exact restricted-frame free-name equation | 9 | 13 for freshness lemma plus conversion | Original 9-line proof replaceable; net **−4** code lines before controls/audits. |
| Generic B10 definitions and relation lemmas | 44 | 15 for abstract framed composition alone | Gross candidate scope only; no checked deletion of these 44 lines. |
| Concrete source/CSLib bridge | No separate removable local block | 93 including its control and audits | Additional validated integration; B9 dependencies retained. |

The two disjoint original candidate scopes total **53 code lines** (72 physical
lines), of which only the 9-line frame proof has an exact checked replacement.
This is the measured candidate set, **not an upper bound on all possible reuse**.
The complete experiments occupy 53 code lines in `CSLibComposition`, 41 in
`FramePort` and 93 in `SourceCSLibBridge`; these include namespace/import
scaffolding, controls and axiom-print commands. The composition core's 15 lines
are contained in its 53; the frame replacement's 13 are contained in its 41.
Do not add contained counts or charge the source bridge twice. Measurement
scaffolding `DependencySnapshot` adds 27 code lines. The main proof was frozen;
no source deletion or migration was performed.

Adapter code roles are separated by the control-fixture and axiom-print blocks:

| Adapter | Proof/interface code | Control code | Axiom-print code | Comment-only lines | Blank lines |
| --- | ---: | ---: | ---: | ---: | ---: |
| CSLibComposition | 21 | 27 | 5 | 10 | 9 |
| FramePort | 22 | 13 | 6 | 9 | 9 |
| SourceCSLibBridge | 83 | 4 | 6 | 7 | 16 |

Imports and namespace declarations count as interface code; literal fixtures
count as controls. These rows partition the adapter totals above.

The exact substitution has negative net line savings, and the CSLib experiment
adds a capability the endpoint does not need. There is therefore **zero
positive net removal demonstrated**, with broader savings **unmeasured**.
A claim that hundreds of existing proof files could have been avoided would
require a much larger checked adaptation or a measured redesign. This audit
provides neither, and does not use raw size as an estimate of elapsed effort.

## Availability at the start and observed engineering costs

The proposal repository begins on 2026-07-31. The formal workflow commit is
`e2cb839defc967b3d56aa814e7a4800b51a7cede`, 2026-09-10 12:43:51 UTC; use that
as the recorded start of this formal development, not as a claim about all
prior exploratory work. All exact pins are in the freeze and source exploration.

| Reference pin | Commit date | Availability conclusion |
| --- | --- | --- |
| CSLib `b777e089…` | 2026-09-11 | Exact pin postdates formal start. Inspected bisimulation-file change `fab37a90…` is dated 2026-09-07; file history reaches 2025-10-07. Relevant generic theory existed earlier, but this does not imply the current whole dependency lock did. |
| SymbolicCryptographyLean `607cf34d…` | 2026-02-18 | Pin predates proposal and formal start. |
| LeanDY `e0705986…` | 2026-07-07 | Pin predates proposal and formal start. |
| AFP `101a3a47…` | 2026-09-11 | Exact pin postdates formal start. Checkout is shallow; this audit does not establish the exact earlier interface revision. |
| CatCrypt-core `91410d23…` | 2026-08-08 | Pin predates formal start, postdates proposal start. |
| VCVio `6d5c7d50…` | 2026-09-10 03:11 UTC | Pin predates the recorded formal workflow commit, postdates proposal start. |

Native CSLib required a separate Lean 4.34.0-rc2 toolchain, its locked dependency
checkout and caches. An optional Reservoir cache request stalled and was
terminated; the successful retry disabled that optional cache and fetched the
explicit Mathlib cache. This is infrastructure cost, not evidence against the
library. Native CSLib sources were unchanged. No full upstream CI run is claimed.

Observed local verification times: the frame port took 1.29 seconds, dependency
traversal 5.14 seconds, and the final main-toolchain composition/source adapter
checks 0.667/0.802 seconds. These are warm local command wall times, excluding
setup and earlier failed attempts. They are **not development-time estimates**.
Namespace resolution and projection reduction also needed routine Lean proof
fixes. No controlled implementation-time comparison was conducted.

## Reproduction and evidence audit

The final main `lake build` log is
`tmp/variable-overlap/source-ballot-secrecy-full-build.log`. It is the completed
proof's integration evidence; subsequent experiments do not modify its sources.
The claim checker and frozen-hash check distinguish it from isolated builds.

From the repository root, with the isolated native CSLib project prepared from
its pinned checkout and lock, run:

```sh
lake env lean docs/research/reuse-adapters/FramePort.lean
lake env lean docs/research/reuse-adapters/DependencySnapshot.lean
python3 scripts/reuse-audit/build-cslib-port.py
python3 scripts/reuse-audit/check-source-adapters.py
python3 scripts/reuse-audit/inventory.py
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/source-ballot-secrecy-full-build.log
```

The compatibility builder copies only the CSLib imports needed for
`Cslib.Foundations.Semantics.LTS.Bisimulation` into
`output/reuse-audit/cslib-main-toolchain`, applies the documented one-line port,
and compiles against the existing main Lean environment without changing Lake
or upstream files. The source checker writes isolated oleans there. For the
native experiment use the exact 4.34.0-rc2 `lake --no-cache build
Cslib.Foundations.Semantics.LTS.Bisimulation` and `lake --no-cache env lean
CSLibComposition.lean` in `output/reuse-audit/cslib-pinned`.

Logs: `tmp/reuse-audit/cslib-bisimulation-build.log`, `cslib-composition.log`,
`cslib-main-toolchain-build.log`, `source-adapters.log`, `frame-port.log`,
`kernel-dependencies.log` and `inventory.log`. Machine-readable port/build
results are under `output/reuse-audit`. All successful adapter theorem axiom
reports use only `propext`, `Classical.choice` and `Quot.sound` (or subsets).
No new axioms, holes or admitted correspondence are introduced. Literal controls
are kernel-checked; no random sampling or failed search is claimed as security
evidence. The native and compatibility builds audit the selected imported
composition theorem's transitive axioms, not every theorem in every reference.

The requested post-proof audit is complete at this measured scope. Broader
framework replacement and computational soundness remain separate research
questions; this report introduces no new development backlog.
