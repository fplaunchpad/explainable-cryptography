# Historical process stages and matching

The normalized twelve-stage process now has checked reachable-state invariants,
matching transitions in both voting worlds, and static equivalence of every
reachable observation frame. It covers two honest voters plus any natural
number of further eligible voters. Every pending input can be any public recipe
using the three handles then available. A failed check stops the process.

This is an intermediate B9 result. The source-calculus operational correspondence
and top-level labelled-bisimilarity theorem remain open. The milestone coverage
stays 8/10 (80%, unweighted); B8 remains complete.

## Source and state mapping

The reality oracle is Cortier–Smyth's [author preprint](https://publications.bensmyth.com/files/Smyth12-attacking-Helios.pdf),
Figure 4 and Appendix B.4/Figures 6–7. The local source is
`_references/cortier-smyth-2013-attacking-and-fixing-helios.pdf`; its text is in
`tmp/cortier-smyth-layout.txt`. The following table records the normalized
residuals; the number of exposed handles is part of each state's type.

| Source relation | Phase | Public handles | Next action |
|---|---|---:|---|
| R1 | `start` | 1 | Private first-voter communication |
| R2 | `firstReceived` | 1 | Publish first ballot as handle 1 |
| R3 | `firstPublished` | 2 | Private second-voter communication |
| R4 | `secondReceived` | 2 | Publish second ballot as handle 2 |
| R5 | `input rs` | 3 | Receive any public recipe on the next eligible voter channel |
| R6 | `check rs r` | 3 | Internal corrected acceptance test |
| R7 | `rejected rs` | 3 | No further step |
| R8 | `sendTally rs` | 3 | Private communication to the trustee |
| R9 | `trusteeReply rs` | 3 | Private return of aggregate partials |
| R10 | `partialReady rs` | 3 | Publish aggregate partial tuple as handle 3 |
| R11 | `resultReady rs` | 4 | Publish result tuple as handle 4 |
| R12 | `done rs` | 5 | No further step |

The public key occupies handle 0 initially. Later attacker ballots are inputs,
so they do not add output handles. After the last required input succeeds,
control proceeds directly to the private tally send. With no extra voters,
the second honest output proceeds there immediately. The voter channel index
is zero-based: input index 2 denotes the source's third eligible voter.

The frame at `resultReady` is the actual `partialFrame`; at `done` it is the
actual `finalFrame`. Earlier views are the corresponding initial-frame prefixes.
Private communication is represented by separate tau steps. The model follows
Figure 4 and the source's explicit `results` definition for per-candidate tally
bindings; Figure 6's final bulletin-board line repeats the last tally index.
The existing authorized tuple-guard correction remains in `Accepted`.

## Checked obligations

[HistoricalProcessSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/HistoricalProcessSyntax.lean)
defines `Phase`, `Action`, `view`, `Step` and unbounded finite `Reachable` paths.
Input and check are distinct: receiving a public recipe does not assume it will
be accepted. Visible outputs bind the next canonical handle; the actual value
is retained in the resulting frame. Inputs carry the complete recipe and the
next eligible voter-channel index.

[HistoricalProcessInvariant.lean](../../ExplainableCrypto/Helios/Symbolic/HistoricalProcessInvariant.lean)
proves `Reachable.wellFormed`: the actual accepted history is public, satisfies
`AcceptsSequence`, and has the appropriate length for the current phase. The
pending recipe is public. These facts follow from transitions without assuming
freshness or universal attacker success. `reachable_done_history` proves that
a reached final state contains exactly all required extra ballots.
`rejected_no_step` and `done_no_step` exclude all outgoing actions.
`Step.output_domain` proves fresh-handle extension; `Step.input_scope` proves
recipe publicness, the three-handle domain, and the correct bounded voter index.

[HistoricalProcessMatching.lean](../../ExplainableCrypto/Helios/Symbolic/HistoricalProcessMatching.lean)
uses B7 to transfer the corrected acceptance test for any public pending recipe
and accumulated public board. `Step.swap` matches every tau or visible action
with the same label and residual phase. `Reachable.swap` and
`reachable_step_iff` derive both directions at every reached stage, without a
predetermined strategy or a premise that the next ballot succeeds.
`wellFormed_view_staticEq` combines B7's derived prefixes with B8's actual partial
and final frames. `reachable_stage_matching` states the observation and both
transition obligations together, preserving reachability after each match.

All matching/static-equivalence claims use `Names.Fresh` and arbitrary valid
ground candidate substitutions. The transition system has the same fixed E/E0,
public-name policy, whole-ciphertext E6 binding and structured-key E5 as B8.

## Controls and experiment

[Ten kernel controls](../../ExplainableCrypto/Helios/Symbolic/HistoricalProcessSPOT.lean)
include actual runs to completion with zero and two extra voters, a received
honest replay that reaches rejection and stops, missing-voter noncompletion,
partial-before-result output, next-voter input order, forbidden restricted-name
input, intermediate public domains, tally two with noncollapsed public-name
equality, and observations at a reached rejected state. Expected outcomes come
from the source order, explicit path constructors and previously checked ballot
fixtures.

The [experiment](../../ExplainableCrypto/Helios/Symbolic/HistoricalProcessExperiments.lean)
uses a local executable stage mirror and a directed one-candidate raw acceptance
oracle. The oracle is only for those fixtures, not a full-E decision procedure.
Four known defects are detected: ignoring rejection, publishing a result before
partials, repeating the old voter channel, and exposing the second ballot early.
Each minimizes to input zero. Positive seeds 1, 7 and 42 each pass 500 cases at
size 40 with no gave-up cases. The 2048-input backstop covers zero through five
extra voters, successful and replay-rejected executions in both swaps.
The general theorems are kernel proofs, independent of this Boolean oracle.

Targeted builds pass: syntax 1003 jobs; invariants and matching 1005 jobs;
experiment 1092 jobs. The invariant's successful build is included in the
matching log; earlier failed elaborations are proof-engineering failures.
Targeted controls pass 1145 jobs.

Latest integrated verification: `lake build` passes **3771 jobs**, with
**2464** nonempty standard-only and **22** axiom-free reports. The claim audit
covers **1500** public theorem entries and **76** current-status documents.
All seven changed Lean sources have current oleans; **962** local
links resolve. No proof holes, custom axioms, warnings or errors were found;
`git diff --check` passes. Log: `tmp/variable-overlap/process-stages-full-build.log`.
The increment adds 28 public theorem audits, including ten kernel controls,
and six definition checks. The targeted controls pass 1145 jobs.

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

## Remaining B9/B10 obligations

The phase machine does not by itself prove that every reduction of the source
applied-pi processes has been represented. The next step is an explicit source
operational correspondence: honest-voter residuals, accumulated substitutions,
private trustee payloads, restricted channels, fresh output binders, and closure
under the source structural/internal rules. Canonical handles need the matching
renaming argument. Public input terms in that source domain must be related to
the `Recipe 3` labels, preserving substitution and evaluation.

Once correspondence is established, B10 can lift the checked stage matching to
the source's weak labelled-bisimilarity obligations and state the full secrecy
theorem for every positive candidate count and total voter count at least two.
The generic source-calculus embedding and this lifting are not assumed as
premises of a theorem named as completed ballot secrecy.

See the [blueprint](helios-proof-blueprint.md), [handoff](handoff.md),
[results ledger](helios-results.md), and [sole task list](../../task%20list.md).
