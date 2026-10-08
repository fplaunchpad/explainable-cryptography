# Guarded board lets and activation

Status: machine-checked. The complete finite board now has construction syntax
that retains the tally lets beneath its preceding inputs, relays and acceptance
guards. Substitution preserves that syntax without capturing input or local
variables. Actual source actions expose the continuation's head lets after an
input, output or ground guard. The compiled complete board and ground election
agree with the existing processes under full-E process congruence.

B9/B10 remain incomplete at 8/10 unweighted milestones. These results do not
establish the remaining general Named operational correspondence or final weak
labelled bisimilarity/symbolic secrecy. Follow the
[blueprint](helios-proof-blueprint.md) and [single backlog](../../task%20list.md).

## Construction and source boundary

Cortier–Smyth Figure 2 gives plain continuations for input, output and guards,
while the surrounding text explains a local let using a restricted active
definition. Figure 4 displays such lets beneath preceding prefixes. The paper
closes structural equivalence under evaluation contexts, which exclude inputs,
outputs, guards and replication. Consequently, the existing proof for the
[active tally block](helios-source-board-tallies.md) cannot simply be lifted
structurally beneath those prefixes.

`GuardedProgram` records these let abbreviations with plain, input, output,
branch and letTerm constructors. `inline` substitutes the let value while
preserving every prefix. `expand` materializes only head lets as restricted
active definitions; at a prefix it uses the compiled plain continuation.
This is a construction convention, not a new source constructor or operational
rule. The public theorem `expand_normalizes` uses source structural rules only
at head lets. No theorem claims generic structural congruence under prefixes.

`subst` lifts the environment under both input and let binders. Identity,
composition and `inline_subst` hold for arbitrary supplied full terms and
variable types. `ofProgram` embeds the existing local tally program, with exact
expansion and inlining equalities. Board register updates and the full tally
program also commute with substitution. These laws do not normalize supplied
terms or remove fields discarded by E.

## Checked interfaces

| Interface | What the public conclusion checks |
| --- | --- |
| `GuardedProgram.receives` | Actual free input to the substituted continuation's expansion. |
| `GuardedProgram.communicates` | Actual source communication, preserving the entire sender continuation. |
| `GuardedProgram.selects_then/else` | Actual reduction under a full ground formula decision. |
| `GuardedProgram.publishes` | Atomic bound output with the complete captured payload and shifted continuation. |
| `guardedCollectBallots_subst`, `guardedBoardStart_subst` | Exact syntax after arbitrary variable substitution. |
| `guardedCollectBallots_receives` | The actual next voter channel and unchanged acceptance guard before tallying. |
| `guardedBoardCheck_last_accepts` | Actual source reduction to the complete explicit tally program. |
| `guardedBoardCheck_last_canonical` | Actual source reduction to the existing canonical tally continuation. |
| `guardedBoardCheck_rejects` | The failed guard reduces to null, retaining no collection continuation. |
| `guardedBoardStart_inline_equivE` | Full compiled board congruence, including both honest relays, every extra input/guard and the ordered outputs. |
| `guardedElectionBody_equivE` | The same congruence for both honest senders, the board and trustee together. |
| `guardedElectionBody_tau/visible` and reverse interfaces | Matching evaluated plain actions, full-E-related visible payloads and EvalEq successors. |

The general board comparisons retain arbitrary candidate count, finite extra
voter count, channel allocation, inputs and earlier ballot lists. They need no
acceptance premise. Guard selection requires the explicit ground guard to hold
or fail. The successful last-input theorem retains the newly received ballot
in the tally. Neither process congruence nor the evaluated action interfaces
are promoted to a Named structural equivalence or final source bisimulation.

## Controls and validation

Twenty public kernel controls retain independent literal input/local-variable
positions, a supplied free None, sender continuation, full fourth proof field,
semantic equality/disequality, both honest input/relay pairs with zero extra
voters, a pending input with no core reduction, fresh last-input acceptance,
replay rejection, both candidate tallies and ordered private/public outputs.
The complete ground election also has an actual first communication. The
fresh/replay fixtures come from the already checked accepted public sequence;
both swapped worlds are covered. The two-candidate expected continuation uses
literal, independently specified raw products from the earlier tally controls.

PBT gate: general structural/substitution proofs and directed kernel controls.
No new randomized cryptographic campaign or search-based security inference is
claimed. Full E, all proof fields, structured-key E5, complete-ciphertext E6 and
existing source action rules are unchanged. The construction convention is
documented against Figures 2–4 in the local paper copy
`tmp/cortier-smyth-layout.txt`; no byte parser is involved.

Integrated verification: `lake build` passes **3966 jobs**. The log reports
**3795** nonempty standard-only and **72** axiom-free results. The claim audit
covers **2881** public theorem entries and **109** current-status documents.
All nine changed Lean sources have current oleans; **1366** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **61** theorem audits,
including **20** public kernel controls, and checks eleven construction and
substitution definitions. The targeted control build passes **1315 jobs**.
Build log: `tmp/variable-overlap/source-guarded-board-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-guarded-board-verification.txt`.

## Files and remaining correspondence

The modules are
[SourceGuardedProgram](../../ExplainableCrypto/Helios/Symbolic/SourceGuardedProgram.lean),
[SourceGuardedActivation](../../ExplainableCrypto/Helios/Symbolic/SourceGuardedActivation.lean),
[SourceBoardProgramSubstitution](../../ExplainableCrypto/Helios/Symbolic/SourceBoardProgramSubstitution.lean),
[SourceGuardedBoard](../../ExplainableCrypto/Helios/Symbolic/SourceGuardedBoard.lean),
[SourceGuardedBoardActions](../../ExplainableCrypto/Helios/Symbolic/SourceGuardedBoardActions.lean),
[SourceGuardedElection](../../ExplainableCrypto/Helios/Symbolic/SourceGuardedElection.lean)
and [SourceGuardedBoardSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceGuardedBoardSPOT.lean).
Their public declarations have type/axiom entries in
[Audit](../../ExplainableCrypto/Helios/Symbolic/Audit.lean).

The board construction, substitution, activation and compiled comparison are
now checked. General Named source correspondence remains open, including canonical
environment/body correspondence through arbitrary structural paths and
remaining admissibility/action matching. The earlier
[open-election application](helios-source-voter-application.md), fresh allocation
and interleaved voter scopes remain checked. The final assembly must connect
these source interfaces to the complete protocol theorem; B9/B10 stay open.

[Independent frame compatibility](helios-source-frame-compatibility.md) now
proves common-policy presentation compatibility and Named.StaticEq transitivity.
Fresh/injective assignment selection and general action matching remain open.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.
