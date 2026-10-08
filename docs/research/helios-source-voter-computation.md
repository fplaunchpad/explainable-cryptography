# Explicit voter computations

B9 now constructs the voter's explicit local computations and proves that they
produce the exact complete historical ballot for every positive candidate count.
Both honest computation blocks fit into the existing allocated-name election
with an actual source structural path, exact action correspondence and the
initial static-equivalence witness. The source model and full E are unchanged.
B9/B10 remain incomplete at 8/10 unweighted milestones (80%).

## Generic local computation compilation

[SourceTermProgram](../../ExplainableCrypto/Helios/Symbolic/SourceTermProgram.lean)
defines a finite construction language with a result term and a let constructor.
Each let binds None and shifts older variables through Some. Its compiler emits
existing Extended variable restrictions and active substitutions, ending in one
output of the final term. This language builds source syntax; it does not add a
new operational rule or replace the existing source semantics.

`eval_value` proves agreement between environment evaluation and substitution
in the computed value. `compile_normalizes` gives an actual Structural path
from the entire compiled program to the exact result output. `compile_no_exports`
shows that the local computation leaves no exported local variables.

## Per-candidate and aggregate lets

[SourceVoterRegisters](../../ExplainableCrypto/Helios/Symbolic/SourceVoterRegisters.lean)
tracks the symbolic key, nonce and vote expressions and the saved ciphertext
and proof registers. The initial ciphertext/proof registers contain bottom.
Processing a candidate saves its ciphertext in a fresh local, then constructs
the full proof with that ciphertext variable as its fourth field. The register
table shifts past both new binders. `afterBind_map` proves the exact evaluated
update. `completed_compute` records precisely which candidate indices have been
processed; an omitted candidate retains its original bottom registers.

[SourceVoterComputation](../../ExplainableCrypto/Helios/Symbolic/SourceVoterComputation.lean)
iterates candidates in `List.finRange` order. It then performs the four Figure 4
aggregate lets: nonce composition, ciphertext product, vote sum and aggregate
proof. All folds are the existing nonempty `foldCandidates`; no identity or
normalizer is inserted. The final tuple contains every saved ciphertext,
every complete component proof and the aggregate proof in their original order.

`voterComponents_eval` proves the exact result for every intermediate index list
and arbitrary substitution. `voterProgram_value` specializes the complete
iteration to literal equality with `General.ballot`, for arbitrary full ground
vote terms. Candidate validity is not needed for this construction equality.
`voterProgram_bindings` proves `2 * (n+1) + 4` local lets, where `n+1` is the
candidate count. `voterProgram_normalizes` connects the complete compiled code
to the exact authenticated ballot output through existing structural rules.

## Allocated-name election correspondence

[SourceComputedVoterElection](../../ExplainableCrypto/Helios/Symbolic/SourceComputedVoterElection.lean)
puts both explicit honest voter blocks beside the existing board and trustee.
The original full name policy and initial exported public-key frame surround
that body. `computedVoterElection_normalizes` gives an actual Named Structural
path to the checked initial source state.

The internal, free-label and bound-output iff theorems preserve arbitrary
source targets and exact labels. They quantify over actual Named actions,
including actions using arbitrary structural representatives. Presentation and
well-formedness witnesses are retained. `computedVoterElection_staticEq` supplies
the initial static clause for the two swapped worlds, under the existing name
freshness premise; it does not claim full behavioral matching or secrecy.

## Controls and source boundary

[SourceVoterComputationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceVoterComputationSPOT.lean)
contains sixteen public kernel controls. A literal two-candidate example checks
all five ballot fields, eight local lets and the actual source output. The
aggregate keeps the raw saved-ciphertext product in its fourth field. Full E
rejects substitution of the other candidate's nonce. Omitting a candidate yields
six lets and a bottom ciphertext slot; that result cannot be the complete ballot.
An open-variable program retains two distinct old variables through both local
binders. A one-candidate example uses six lets and retains a nonliteral ground
vote expression exactly. The expanded election is well-formed, has its initial
static witness and performs a real first private communication.

The independent source oracle is Figure 4 of Cortier–Smyth, in the local
research reference and its text at `tmp/cortier-smyth-layout.txt:1174–1195`.
The expected literal register/tuple values were written separately from the
program evaluator. These are general structural/substitution proofs and kernel
controls, with no new randomized cryptographic campaign or inference of
security from failed search.

Figure 4 interleaves fresh nonce restrictions with per-candidate lets. The
subsequent [scope increment](helios-source-voter-scopes.md) now derives that
placement in the complete initial source election and supplies a fresh common
allocation for arbitrary full ground candidate terms. The later
[open-application proof](helios-source-voter-application.md) now certifies the
parameterized voter and complete election under all scopes.
The later [guarded board construction](helios-source-guarded-board.md) retains
the tally lets beneath the input/guard chain and proves source activation and
compiled congruence. [Independent frame compatibility](helios-source-frame-compatibility.md)
now proves Named static transitivity. Canonical environment/body correspondence
through arbitrary Named action paths and remaining admissibility/matching stay open. B10's source weak labelled bisimilarity and
symbolic secrecy theorem remain unproved. See the
[blueprint](helios-proof-blueprint.md) and [task list](../../task%20list.md).

Integrated verification at this voter-computation checkpoint: `lake build` passes **3937 jobs**. The log reports
**3556** nonempty standard-only and **62** axiom-free results. The claim audit
covers **2632** public theorem entries and **105** current-status documents.
All seven changed Lean sources have current oleans; **1298** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **37** theorem audits,
including **16** public kernel controls, and explicitly checks eleven
construction/compilation definitions. Targeted controls pass **1144 jobs**.
Build log: `tmp/variable-overlap/source-voter-computation-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-voter-computation-verification.txt`.

The subsequent [board tally increment](helios-source-board-tallies.md) now
expands the named tally definitions at the reached tallying stage. Source
continuations beneath earlier inputs/guards remain a correspondence obligation.
