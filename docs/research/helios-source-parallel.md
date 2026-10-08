# Source parallel structure and election residuals

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

B9 now has an exact characterization of the source parallel structural laws,
an exact characterization of internal reduction modulo those laws, and literal
process residuals realizing every internal stage transition. These are
machine-checked source-bridge results. The internal converse is now checked in the record above; restrictions,
active substitutions and visible labels remain open; B9/B10
remain incomplete at 8/10 milestones (80%, unweighted).

## Parallel structural laws

[SourceParallelSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceParallelSyntax.lean)
defines `Agent.ParEq` from the source Par-0, Par-A and Par-C rules, equivalence
closure and parallel evaluation contexts. It does not allow rewriting below
an input, output or conditional. `threadList` flattens only active parallel
structure, deleting nulls and retaining each complete guarded process as one
thread. `threads` is its multiset, preserving multiplicity.

[SourceParallelStructure.lean](../../ExplainableCrypto/Helios/Symbolic/SourceParallelStructure.lean)
proves `parEq_iff_threads` in both directions. Preservation follows by induction
on structural equivalence. Completeness reconstructs a process from its thread
list and transports list permutations using the parallel laws. Thus the multiset
is an exact presentation of this structural fragment, not merely an invariant.
`ParEq.subst` preserves these laws under the checked capture-avoiding substitution.

`Agent.Tau` is one `CoreStep` preceded and followed by `ParEq`. It is not a
reflexive-transitive closure. The private-communication core still includes
direct receiver substitution; its relation to the paper's atomic Comm and
active substitutions remains to be established.

## Complete internal-redex characterization

[SourceParallelReduction.lean](../../ExplainableCrypto/Helios/Symbolic/SourceParallelReduction.lean)
proves `tau_iff_threadReduction`: exactly one primitive communication or enabled
conditional redex is replaced, leaving a real parallel context unchanged.
`ThreadReduction` uses actual processes for its context, so its converse does
not assume arbitrary thread bags are realizable. The forward proof extracts the
redex from core parallel contexts and uses structural thread equality. The
reverse proof constructs a core reduction in that context and uses structural
completeness on both sides. Parallel and structural closure of Tau are proved.

[SourceParallelGuards.lean](../../ExplainableCrypto/Helios/Symbolic/SourceParallelGuards.lean)
derives a necessary readiness condition in the active threads: a conditional
or a same-channel output/input pair. Null and isolated guarded inputs/outputs
therefore have no Tau step, even after arbitrary parallel restructuring. This
is a necessary condition; it does not claim that every conditional is enabled
without consulting its full-E guard.

## Literal election residuals

[SourceElectionResiduals.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionResiduals.lean)
defines the actual finite process for each of the twelve stage forms. The board
keeps the evaluated accepted history and any pending guard. Honest voters and
the trustee remain in parallel until their respective sends complete. The
rejected board is null, but its trustee is still waiting for the private tally
input. The rejected residual therefore retains the trustee rather than erasing
it. The completed residual is null.

The next-input/tally boundary is expressed uniformly by `residual_afterAccepted`.
It uses the same voter count and actual source board values, with each received
recipe interpreted in the initial frame. `source_accepts_iff` connects the stage
acceptance predicate to those literal ground board values.

[SourceElectionSilent.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionSilent.lean)
proves `residual_tau_step`: every internal stage transition has one Tau step
between its literal residuals. The first honest communication rearranges the
four-component election, delivers the ballot, removes the completed null voter
and retains the other voter, public relay and trustee. The second receive does
the corresponding three-component step. Accepted/rejected checks preserve the
waiting trustee; tally delivery and reply use the actual source payloads, with
explicit parallel commutation for the reply. General theorems rule out Tau at
rejected and completed residuals.

This is the stage-to-source direction for internal steps. The generic two-way
redex characterization is available for proving the election-to-stage direction,
and the subsequent internal-correspondence proof now uses it for every in-range
residual. The soundness lemma does not require channel distinctness; the checked
converse explicitly assumes Channels.Fresh to exclude unintended communications.

## Controls and remaining obligations

Ten kernel controls in
[SourceParallelSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceParallelSPOT.lean)
check legal parallel rearrangement, retained duplicate outputs, preserved
sequential order, a guarded hidden communication that cannot run, and mismatched
channels that remain unable to communicate after restructuring. Actual election
controls cover both honest handshakes and both consecutive private tally/reply
steps. Rejection retains a non-null trustee with no internal step; completion
is null and internally quiet.

This increment proves structural algebra and direct operational correspondence,
with kernel controls. It adds no randomized security campaign. Elaboration
issues concerned type inference, finite-index presentation, dependent constructor
names and redundant simplifier arguments; the claims were not weakened. No
search failure is used as evidence of security.

Internal converse classification is now proved. Next: connect public input
and output labels and private-channel restrictions. In particular,
the rejected trustee has a syntactic input prefix; restriction must prove that
it cannot receive a public action. Outer fresh-name allocation, voter lets,
exported public-key/output substitutions, scope rules and name alpha-equivalence
also remain part of the extended-source bridge. ParEq is the parallel fragment
of source structure; its completeness is not a completeness theorem for those
additional source rules. Source weak labelled bisimilarity and the full symbolic
secrecy statement remain open.

Latest integrated verification: `lake build` passes **3791 jobs**, with
**2597** nonempty standard-only and **36** axiom-free reports. The claim audit
covers **1647** public theorem entries and **80** current-status documents.
All nine changed Lean sources have current oleans; **1005** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-parallel-full-build.log`. This increment
adds 46 theorem audits, including ten kernel controls, and ten definition
checks. Targeted controls pass 1164 jobs.
