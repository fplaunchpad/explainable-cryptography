# Exact internal source correspondence

Current internal frontier: [general Named communication and actual election
matching](helios-source-communication.md) are now checked without injectivity.
Arbitrary Named conditional correspondence, required target presentation/relation
invariants and final secrecy remain open. Earlier open internal statements below
describe their checkpoint; B9/B10 are still incomplete.

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

B9 now has both directions of internal correspondence for the literal finite
election residuals modulo the source parallel laws. Every arbitrary internal
source target is parallel-equivalent to a stage-prescribed residual, and every
internal stage step has such a source realization. Internal steps match between
the two voting worlds, including arbitrary parallel-equivalent representatives.
These are machine-checked results. Visible labels, restrictions and the extended
source calculus remain open, so B9/B10 stay incomplete at 8/10 milestones
(80%, unweighted).

## Explicit source premises

[SourceChannelPolicy.lean](../../ExplainableCrypto/Helios/Symbolic/SourceChannelPolicy.lean)
defines `Channels.Fresh`: voter channels are injective, broadcast and trustee
channels differ from every voter channel, and broadcast differs from trustee.
The canonical allocation satisfies every condition. This is a naming premise;
it does not enforce restriction or hide a channel operationally.

The converse also uses `phase.inRange extra`. In an input phase, at least one
eligible voter must remain. Otherwise truncated subtraction makes the literal
collection body send the tally, although the stage constructor still says input.
Stage reachability already proves this range condition. Neither premise is an
assumed reduction classifier or determinism callback.

## Redex and phase inversion

[SourceTauInversion.lean](../../ExplainableCrypto/Helios/Symbolic/SourceTauInversion.lean)
unpacks the previously proved complete primitive-redex/context characterization.
If the only matching pair has a given channel, payload and continuations, every
Tau consumes that exact pair. Cancellativity of active-thread multisets then
forces equality of the unchanged contexts and hence parallel equivalence of
all targets. A corresponding result covers one conditional and input-only
waiting processes; full-E guard truth excludes the opposite branch.

[SourceTauShapes.lean](../../ExplainableCrypto/Helios/Symbolic/SourceTauShapes.lean)
discharges these generic uniqueness conditions for the actual small parallel
shapes: the four initial components, one voter output with board/trustee inputs,
a private output/input pair, and a conditional with a waiting trustee. It also
rules out Tau in input-only networks and outputs that have no same-channel input.

[SourceResidualQuiet.lean](../../ExplainableCrypto/Helios/Symbolic/SourceResidualQuiet.lean)
uses the channel policy to block internal steps before each honest public relay.
An in-range pending voter phase is also internally quiet. The final output
prefixes, rejected waiting trustee and completed null process reuse the earlier
quietness theorems.

[SourceResidualDeterminism.lean](../../ExplainableCrypto/Helios/Symbolic/SourceResidualDeterminism.lean)
proves `residual_tau_deterministic` for every in-range stage and separated
channel assignment. This includes arbitrary ground Tau targets after arbitrary
parallel restructuring. The proof discharges every redex-shape condition from
the literal residual syntax and channel policy.

## Correspondence and matching

[SourceInternalCorrespondence.lean](../../ExplainableCrypto/Helios/Symbolic/SourceInternalCorrespondence.lean)
proves `residual_tau_iff`:

```text
Tau (residual phase) target
  iff there is a stage tau step phase → next
      and target is ParEq to residual next.
```

The forward direction first rules out quiet phases, retains both acceptance
outcomes, and identifies an actual stage step. The earlier source realization
of that step plus proved target determinism identifies the arbitrary source
target. The reverse direction realizes the stage step and applies the given
target structural equivalence. `reachable_residual_tau_iff` obtains the range
premise from stage reachability.

`reachable_source_internal_matching` allows both source-side processes to be
arbitrary parallel-equivalent representatives of corresponding residuals. An
internal step on either voting world is classified, transported using the
checked stage matching and reachable public-history/pending-input invariants,
and realized on the other world. The target retains a reachable next stage and
its exact residual up to parallel structure. Fresh base names are explicit in
this two-world result because it invokes the earlier cryptographic stage theorem.
This theorem concerns internal steps; it is not labelled bisimilarity or a
frame-secrecy result by itself.

## Controls and boundary

Eleven kernel controls in
[SourceInternalSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceInternalSPOT.lean)
check canonical separation, the first handshake and all its targets, mandatory
honest relays, pending-voter quietness, exact accepted/replayed check targets,
and explicit existence of both check outcomes. The first receive cannot discard
the three remaining active components.

Two retained counterexamples demonstrate necessary premises. With coincident
broadcast/trustee channels, the second honest public ballot silently communicates
with the waiting trustee, although its stage has no Tau constructor. Separately,
an exhausted collection mislabelled as an input phase has an actual tally Tau
that its stage lacks. These are constructed source reductions, not failures to
find a desired proof. They refute removing channel separation or inRange from
the general converse.

The increment proves structural inversion and exact internal correspondence,
with explicit kernel controls. It adds no randomized security campaign. Failed
elaborations concerned reducing a stage match before rewriting and unfolding
the range predicate before deciding concrete inequalities. No claim was weakened.

The evaluated wrapper now supplies public recipe/output labels and fixed
private-channel filtering, including the retained rejected trustee. Full
visible classification and exact captured-frame agreement are now checked in
that wrapper. Fresh active exports now have atomic bound-output derivations and
exact frame capture after canonical handle renaming. Recipe input and internal
steps now derive beside the actual public frame. Next derive name restriction
and the remaining full source correspondence. Outer fresh allocation, voter lets,
scope, name alpha-equivalence and the full active-frame converse remain in the
source bridge. Variable well-formedness and preservation from actual frame states
are now proved for the implemented rules. Atomic Comm with active lets now derives the evaluated internal
rules in the variable/active fragment. Only after these and the observations are connected can the
source weak labelled bisimilarity and full symbolic secrecy theorem be claimed.

Latest integrated verification: `lake build` passes **3798 jobs**, with
**2631** nonempty standard-only and **36** axiom-free reports. The claim audit
covers **1681** public theorem entries and **81** current-status documents.
All nine changed Lean sources have current oleans; **1016** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-internal-full-build.log`. This increment
adds 34 theorem audits, including eleven kernel controls, and five definition
checks. Targeted controls pass 1171 jobs.
