# Literal source election body and acceptance formula

[Historical symbolic ballot secrecy](helios-source-coordinated-phases.md)
is now machine-checked, integrated and audited. B1–B10 meet their acceptance
conditions. scopedVoterElection_ballot_secrecy proves source weak labelled
bisimilarity of the actual swapped scoped elections, for arbitrary valid ground
candidates and finite administration size under documented name, nonce/parameter
and channel freshness. SourceElectionRelation preserves all actual source actions,
complete frames, shared handle coordinates and private policies. The final
interface assumes no source correspondence, bisimulation or static equivalence.
The historical component-weeding protocol and documented tuple-tail correction,
full E/E0, attacker observations and rejection behavior are unchanged. Independent
positive/negative controls and both refuted shortcuts remain. The [retrospective reuse audit](helios-reuse-retrospective.md) is complete;
computational security is a separate extension.

B9 now has the complete finite bulletin-board and trustee bodies in the source
process AST, a finite acceptance formula exactly equivalent to `Accepted`, and
checked substitutions and direct core reductions for those bodies. This closes
the formula and finite-body construction gaps. The operational correspondence
for the whole restricted source election, including all structural and labelled
steps, remains open. B10's source secrecy theorem is also open; coverage stays
8/10 milestones (80%, unweighted).

## The finite guard

[SourceElectionGuard.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionGuard.lean)
constructs a `Formula`, rather than supplying an opaque acceptance predicate.
An empty conjunction is represented by `ok = ok`, an allowed source formula.
The guard tests the aggregate proof, all individual candidate proofs, the
remaining tail after `fieldCount n` fields, and every earlier/current candidate
pair for ciphertext reuse. It uses the documented `snd^fieldCount` correction,
not the erroneous printed projection. The parameter `n` denotes `n+1` candidates.

`electionGuard_holds` proves equivalence to `Accepted` under every ground
substitution, including for malformed ballots. `electionGuard_ground` specializes
to closed messages, and `electionGuard_subst` proves exact syntax agreement under
substitution. `electionGuard_public` checks the restricted-name policy throughout
the formula whenever its key, board and ballot are public recipes.

`evaluated_guard_accepts` connects this literal formula to `Process.accepts`
in the initial public frame. `evaluated_guard_swap` derives equal truth values
from B7's initial static equivalence and publicness of the generated guard.
No new cryptographic equality oracle, search result or acceptance callback
replaces B7's theorem.

## The finite board and trustee

[SourceElectionSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionSyntax.lean)
represents channel names separately from base-message names. `Channels` records
the broadcast channel, trustee channel and ordered voter channels. Its canonical
instance uses 0, 1 and `i+2`, respectively. Distinct numbers do not enforce
privacy: the source bridge must restrict the trustee and two honest channels.

`boardStart` receives the first honest ballot and publicly relays it, then
`boardSecond` receives and relays the second. `collectBallots` recursively waits
for the remaining voters, in order. The next channel is determined by the number
of already collected extra ballots. Each input is followed by `electionGuard`
on the old board; Then appends the new ballot once, while Else is null. There
is no attacker-ballot broadcast, skipped last input, or continue-after-rejection
branch. With zero remaining voters, `boardFinish` sends the full tally tuple on
the trustee channel, receives the partial tuple, broadcasts it, and broadcasts
the ordered results. `trusteeAgent` receives the tally tuple and returns the
literal source partial-decryption expression.

`electionBody` puts the two honest ballot outputs, board and trustee in parallel
after names have been allocated. It uses the established ballot construction
and arbitrary valid ground candidates. [Explicit voter let blocks](helios-source-voter-computation.md)
now have an actual structural path to this body and to the existing restricted
initial election with its public-key frame. [Interleaved nonce restrictions](helios-source-voter-scopes.md)
now normalize in that complete initial election, and arbitrary full ground
parameters admit a fresh common allocation. [Open voter/election application](helios-source-voter-application.md)
now supplies an exact source instantiation certificate under every scope,
while preserving the exported public-key variable.
[Explicit board tally lets](helios-source-board-tallies.md) normalize at the
reached tallying stage. [Guarded board construction](helios-source-guarded-board.md)
now records those lets beneath the full preceding input/guard chain, proves
substitution and actual source activation, and compares the compiled complete
board with this generator under full-E process congruence. This does not add
structural closure beneath prefixes or discharge general Named correspondence.

[SourceElectionBinding.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionBinding.lean)
proves substitution agreement for the entire generator, by induction on the
remaining voter count with arbitrary variable types and environments. Inputs
shift all old values past the fresh binder. `collectBallots_bind` proves that
delivery constructs exactly the guard on the previous board and the continuation
with the received ballot appended. The first/second honest input laws preserve
their public relays. Trustee/result body substitutions reuse the previously
checked [payload expressions](helios-source-payloads.md).

## Direct reductions and controls

[SourceElectionReduction.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionReduction.lean)
checks first/second honest communications, delivery to the next input, accepted
and rejected checks, tally delivery to the trustee, and reply delivery to the
board. These are ground `CoreStep` statements with exact source continuations.
Public adversarial delivery is shown as communication with an explicit sender;
the visible input rule and its recipe scope are not yet derived here. The reply
lemma explicitly places its sender on the left: it does not silently assume
parallel commutation or erase null components.

The twelve kernel controls in
[SourceElectionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionSPOT.lean)
retain source-derived expected channels and order, a real accepted last ballot,
replay stopping, an omitted-board guard mutant, cross-candidate reuse, preserved
honest input positions, and partial-before-result output order. A two-candidate
source reply produces the previously established distinct zero/one results.
The cross-candidate negative uses full E projection proofs, not raw syntax
inequality. The omitted-board mutant accepts a valid ballot on an empty board
and the actual guard rejects it on a board already containing that ballot.

These are finite formula equivalences, structural substitution laws and direct
reductions, checked generally and against kernel controls. This increment adds
no randomized campaign and makes no security claim from search failure. Earlier
fixture campaigns keep their explicitly bounded scope. Elaboration issues were
reserved identifier spelling, lambda-form list-map simplification, explicit
source-definition unfolding, and a missing concrete membership witness; the
claims were not weakened. An initial control description overstated retained
key syntax when zero remaining voters makes the key unused; the corrected
control claims only the two honest messages' preserved positions in the tally.

The next B9 work is the source extended-process/structural/restriction layer and
a complete characterization of election residuals and visible labels, including
fresh public output variables. The direct substitution rule still needs its
connection to Figure 3's atomic Comm and active substitutions. The finite body
has no replication or dynamic channel variables; source correspondence must
justify the finite static-channel representation for this election. B9/B10
remain incomplete until these obligations and source labelled bisimilarity are
proved.

Latest integrated verification: `lake build` passes **3784 jobs**, with
**2556** nonempty standard-only and **31** axiom-free reports. The claim audit
covers **1601** public theorem entries and **79** current-status documents.
All seven changed Lean sources have current oleans; **995** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-election-full-build.log`. This increment
adds 42 theorem audits, including twelve kernel controls, and eleven definition
checks. Targeted controls pass 1157 jobs.
