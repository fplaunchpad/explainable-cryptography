# Coordinated phases across private-name freshening

## B10 acceptance: historical symbolic ballot secrecy

Claim: swapping the two honest valid ground candidate substitutions in the
actual repaired historical scoped election preserves source weak labelled
bisimilarity. Status: **machine-checked, integrated and audited; B1–B10 complete**.
Formal oracle: scopedVoterElection_ballot_secrecy in
[SourceBallotSecrecy.lean](../../ExplainableCrypto/Helios/Symbolic/SourceBallotSecrecy.lean),
with source_reachable_weak_bisimulation and source_election_weak_bisimilar.
The theorem has arbitrary n (n+1 candidates), arbitrary valid ground candidate
substitutions and arbitrary extra : Nat (extra administration inputs after the
two honest voters). Its only explicit proof hypotheses are Names.Fresh,
NoncesFreshFor each candidate value family and Channels.Fresh. Candidate validity
is carried by CandidateSubstitution. No correspondence, bisimulation, static
observation, target presentation, program-class or normalization premise remains.

Definition audit against the pinned author preprint's Definition 2 (§5.1.2,
printed p. 23), with the already documented finite static-channel source scope:

| Historical obligation | Checked source formulation |
| --- | --- |
| Symmetric relation on closed extended processes | Named.IsWeakLabelledBisimulation.symmetric/closed; closedness follows from actual complete presentations. |
| Static equivalence of full frames | observations uses Named.StaticEq, including both original structural presentations and every public full-E recipe equality. |
| Internal action matched by finite internal closure | internal uses original Named.Reduction and its reflexive-transitive closure WeakReduction. |
| Labelled action with internal prefixes/suffixes | free and bound use original FreeStep/BoundOutput inside WeakFreeStep/WeakBoundOutput. |
| Free variables within the public domain | free retains LabelScoped and the complete original recipe; the constructed source match in fact works for every actual raw input. |
| Fresh bound output | Option.none is fresh; every old handle remains Option.some. Both full targets use the exact outputHandle bijection; SourceElectionRelation.reindex preserves arbitrary common finite handle permutations. |
| Largest relation | WeakLabelledBisimilar is the existential union of witness relations; weakLabelledBisimilar_isWeakLabelledBisimulation proves that union itself satisfies all clauses. |

The full source relation proved in B9 supplies these clauses. Each actual
internal challenge has an actual single-step partner; every public challenge
has an actual partner action with zero surrounding internal steps. Both return
the same successor-preserved relation with actual execution provenance. The
weak formulation permits all finite internal prefixes and suffixes. The final
secrecy theorem instantiates this witness with SourceElectionRelation.initial,
which derives all fields from the actual scoped protocol. The normalized initial
source theorem is a consequence, not a replacement target.

Reality oracle: the existing pinned historical source, equations, source rules,
scoped election and the documented tuple-termination correction. The correction
uses the proper tuple tail test; this is the corrected historical symbolic
claim, not the uncorrected printed guard or a computational security theorem.
No source rule, attacker capability, cryptographic equation, rejection behavior,
nonce policy or upstream pin was changed for B9/B10 closure.

Falsifier and negative control: a live output process and a stopped process have
the same complete static frame but are not WeakLabelledBisimilar. Even arbitrary
silent steps cannot create the stopped process's missing publication channel.
This checked control prevents static equivalence or a stuck witness from standing
in for dynamic secrecy. Other controls instantiate arbitrary administration size,
the reverse voting direction, actual replay input followed by rejection under
the final relation, and missing-domain exclusion. The existing homomorphic,
accepted/rejected ballot, fresh-output, private-channel and local-guard controls
remain. The cyclic semantic-equality reconstruction shortcut and fixing the new
output policy to the old frame policy remain checked counterexamples.
PBT gate: retained independent seeded gates and deterministic controls run in the
main build; this logical assembly adds directed kernel controls and universal
relation proofs, not a new randomized source search. Search failure is not used
as evidence. The only failures in this assembly were redundant simp arguments;
no theorem weakening or trusted definition change was needed.

Integrated evidence: the clean targeted controls and required `lake build`
pass. The final full log contains 4967 standard-only nonempty and 103 axiom-free
reports; the claims checker covers 4058 public theorem entries and 132 current
status documents. Seven changed oleans are current. No holes, custom axioms,
warnings or errors occur in scope; `git diff --check` passes. Eleven public
theorem audits, five controls and five weak-semantics definition audits were
added. Log: `tmp/variable-overlap/source-ballot-secrecy-full-build.log`.

B1–B10 acceptance is complete. No symbolic source-correspondence, action,
frame, freshness or final-secrecy obligation remains open at the stated scope.
The requested [retrospective reuse audit](helios-reuse-retrospective.md) is also
complete: frozen dependency measurements and checked source/CSLib and frame
adapters establish the measured reuse boundary. It is follow-on evidence, not a
premise of this theorem. Computational soundness, concurrent elections and other
protocol extensions remain separate.

The following checkpoint narratives are historical; their open B9/B10 claims
are superseded by the completed theorem and audit above.


## B9 acceptance: one successor-preserved source relation

Status: **machine-checked, integrated and audited; B9 complete**. B10 remains
open. SourceElectionRelation records both actual finite execution histories,
the common reached historical phase, a complete public-handle bijection, shared
base/channel permutations, complete joint source openings and both actual full
frame presentations. Its definition permits either voting order; symm swaps
the complete evidence. It does not assume action correspondence or secrecy.

SourceElectionRelation.staticEq proves actual Named.StaticEq on the original
raw handle domain. SourceFrameReindexing reorders every active provider using
only original parallel laws and existing Mathlib finite-list permutations;
full public-recipe substitution proves the observation transport. The adapter
retains every complete payload and needs a bijection, not an arbitrary map.

SourceElectionRelation.structural and reindex preserve the relation and both
actual executions. internal uses the checked general raw matching theorem;
input preserves the exact original raw recipe after inverse handle transport;
free also excludes old-handle outputs via the reached historical invariant.
bound preserves the same public channel, every old Option.some coordinate and
the fresh Option.none coordinate. Both targets use the same outputHandle
bijection and return the same relation, with extended execution provenance.
Private name policies are retained or jointly refreshed by the existing input
clause. These are actual original-source actions in both directions.

SourceElectionRelation.initial derives every field from the actual scoped
elections, name freshness and the documented nonce/parameter freshness. The
channel-freshness premise is used by matching. The initial theorem assumes no
normalization, presentation, extraction, program class or missing correspondence.
The existing arbitrary-finite-execution frame theorem supplies the independently
checked reachable reconstruction acceptance condition.

Seven new controls retain distinct values under simultaneous handle permutation,
reject a permutation applied to only one observation frame, construct actual
initial membership, preserve one relation through a real replay input followed
by rejection, preserve a nonidentity reached-handle permutation, and exclude an
unexported initial domain. Existing actual fresh-publication, local guard,
private-channel, cyclic, rejection and cryptographic controls remain integrated.
No new random Structural campaign or upstream build is claimed. Failures were
proof engineering: finite-list theorem qualification, identity function reduction,
explicit Fin numeral types and use of finCongr rather than a generic type cast.

Integrated evidence: the targeted controls and required `lake build` pass.
The full log contains 4951 standard-only nonempty and 103 axiom-free reports;
the claim checker covers 4047 public theorem entries and 132 current-status
documents. Five changed oleans are current, all 1646 local links resolve, and
no holes, custom axioms, warnings or errors occur in scope. `git diff --check`
passes. Twenty-three public theorem audits, seven controls and two definition
audits were added. Log: `tmp/variable-overlap/source-election-relation-full-build.log`.

Remaining B10 acceptance obligations:

1. **Open — source_reachable_weak_bisimulation.** Package the completed
   SourceElectionRelation clauses as one symmetric source weak labelled
   bisimulation. Use actual Named.StaticEq, original Reduction/FreeStep/
   BoundOutput and finite internal closures. Keep full label domains and the
   typed fresh output coordinate explicit. Check this definition against the
   historical Definition 2; no conditional correspondence premise is needed.
2. **Open — source_election_weak_bisimilar and
   scopedVoterElection_ballot_secrecy.** Instantiate that relation with the
   actual scoped initial elections using SourceElectionRelation.initial and
   documented name, nonce/parameter and channel freshness. Quantify arbitrary
   valid ground candidates, positive candidate count and finite administration
   size. Retain full E/E0 observations, rejection and independent positive and
   negative controls; run the public theorem, full build and writing audits.

The retrospective reuse audit remains after B1–B10 secrecy completion.

The following checkpoint narratives are historical and do not reopen B9.


## Actual raw internal availability and matching

Status: **machine-checked, integrated and audited** for general raw internal
availability and each reached internal matching clause. B9's combined relation
and B10 remain open.

SourceReadyPrefixExtraction derives actual ready input/output prefixes under
original finite local scopes. SourceCommunicationAvailability extracts both
compatible heads from the same raw process, retains the untouched context and
uses the original message_communication derivation. Its Named version retains
all private restrictions. SourceRawCommunicationMatching proves the intermediate
non-check phase result; its explicit conditional exclusion is now removed by
SourceRawInternalMatching.source_reachable_internal_match.

The conditional gap closes without changing the ground-guard reduction rules.
SourceLocalCodePrefix.exists_local_code_prefix extracts all existing local scopes,
provider forest and full live code from arbitrary original Extended syntax.
SourceOpenLocalPresentation.BinderStructural.open_local_frame uses the completed
actual output-presentation theorem to derive a full presentation after opening
one existing local. The auxiliary output is proof instrumentation, not an action
inserted into the historical protocol. SourcePresentedInternalAvailability then
opens that finite prefix inductively. At the binder-free leaf, the actual frame
path rewrites the retained providers beside unchanged code; activeFrame_apply
grounds the code, including guards and both continuations. Full EvalEq transports
the given internal Tau, tau_ground_derivable produces the original reduction,
and exact inverse variable bijections reclose all original local/name scopes.

Extended.internal_available_of_presentation requires only an actual current
frame presentation, a complete realization and its internal Tau. The named
JointOpening.internal_available requires only the actual current presentation,
full joint opening and canonical Tau. Prefix, forest, opened presentations and
guard grounding are derived. Fresh canonical name permutations are bijections,
so both positive and negative guards transport. source_reachable_internal_match
uses this availability together with the reached phase invariant and checked
phase determinism; both raw successors retain complete presentations and full
static equivalence at the same exact handle cast. No check-phase, extraction,
normalization, target presentation or missing-correspondence callback remains.

Seven directed controls include a local guard compared against a dependent
public provider in both truth directions, distinct then/else output channels,
communication across two separate local scopes, private raw communication,
mismatched-channel impossibility, the retained cyclic presentation exclusion,
and actual historical component-replay rejection with a padded raw partner and
full successor observations in both voting directions. Existing nested-prefix,
private-output and cryptographic positive/negative controls remain. No new
random Structural search or new historical-model validation is claimed.

Failures were proof engineering: dependent local-variable types needed explicit
renaming identities, frame rewrites needed their actual structural theorem, and
finite casts needed explicit target types. A fixture's proposed intermediate
syntactic equality omitted substitution of its retained public provider; it was
false at that intermediate point. The correction applies existing activeFrame_apply
before asserting the independently specified ground guard. The public theorem
and all source rules remain unchanged. The semantic-equality-only structural
shortcut and fixed-old-policy output shortcut remain refuted.

Integrated evidence: `lake build` succeeds; the clean targeted control build
also succeeds. The current full log contains 4926 standard-only nonempty and
103 axiom-free reports. The claims checker covers 4024 public theorem entries
and 132 current-status documents. Ten changed Lean oleans are current; all 1684
local links resolve. No holes, custom axioms, warnings or errors were found in
scope; `git diff --check` passes. Twenty-seven public theorem audits include
seven controls, with both guard truth values quantified. Log:
`tmp/variable-overlap/source-raw-internal-full-build.log`.

Remaining B9/B10 acceptance obligations:

1. **Open — integrate all clauses into one source relation.** The individual
   source_reachable_internal_match, source_reachable_input_match and
   source_reachable_bound_match clauses are now checked. Package their current
   phase, actual execution provenance, full presentations and shared handle/name
   coordinates, and prove the same relation at every pair of actual successors.
   Cover structural changes, internal reductions, unchanged public input labels,
   fresh outputs, reindexing and both voting directions. Preserve old-handle
   output exclusion and rejection. Intended declarations: SourceElectionRelation
   with structural, internal, free, bound and reindex closure; its initial scoped
   membership must derive all fields from the documented freshness conditions.
2. **Open — source_reachable_weak_bisimulation and
   source_election_weak_bisimilar.** Assemble the source-level weak labelled
   bisimulation from the completed B9 relation. The observations must be actual
   full Named.StaticEq presentations and actions must use the original Named
   semantics, with exact fresh output domains. Prove symmetry and preservation;
   do not assume correspondence at this interface.
3. **Open — scopedVoterElection_ballot_secrecy.** Transfer to the actual scoped
   elections with documented name, nonce/parameter and channel freshness,
   arbitrary valid ground candidates and finite administration size. Audit the
   full E/E0 observations, rejection, public hypotheses and independent controls.
   Stage matching, equal tallies and static equivalence alone are insufficient.

The retrospective reuse audit stays after B1–B10 secrecy completion.

The following checkpoint narratives are historical; their next-step prose is
superseded by the current dependency map above.


## Actual raw input and bound-output matching

Status: **machine-checked, integrated and audited** for B9's visible action
availability and successor matching. B9 internal matching and B10 remain open.

SourceVisibleReadiness defines HasInput and HasOutput only at evaluation depth.
Substitution and full EvalEq preserve those ready prefixes; arbitrary name maps
preserve readiness at the mapped channel. The original source input rule and
message_output derivation then supply real Extended actions under arbitrary
parallel and local-variable contexts. The full raw input recipe is shifted
correctly under each local binder, and bound output keeps the complete payload
and exports one fresh Option coordinate. No guard is crossed and no action rule
is added.

SourceJointVisibleAvailability lifts these results to Named.JointOpening through
an actual fresh full name opening. JointOpening.input_available constructs an
actual input on the raw process with the unchanged recipe; allocation freshness
is derived against every name in that label and the raw process. The theorem
requires a public channel and a ready canonical prefix. It allows any raw
recipe for action existence; matching its canonical evaluated successor uses
the separate public-recipe premise, as the existing public_input_target requires.
JointOpening.bound_available similarly constructs an actual raw bound output
on the same public channel, preserving the full restriction prefix. Neither
requires a target presentation or an assumption of action correspondence.

SourceRawInputMatching.source_reachable_input_match combines actual current
presentations and the existing coordinated fresh-input classification with the
new raw-partner action. Both actual successors have reached phases, full
presentations at jointly refreshed policies and Named.StaticEq observations.
The exact original recipe remains in the partner's action label, even when it
contains a formerly private spelling. SourceRawOutputMatching.
source_reachable_bound_match uses the actual publication and checked stage swap
only to identify the partner's enabled output, then constructs that output in
the raw partner itself. Output target closure, constructive presentation and
phase alignment preserve both full frames under the same Option/outputHandle/
Fin.cast domain bijection. Static equivalence covers every handle there; it does
not replace matching.

Eight directed controls cover full-SPK input labels, fresh output domains,
prefix-blocked nested actions, wrong channels, private ready inputs/outputs that
cannot escape, a real formerly-private-literal input from nonidentity name
coordinates with a padded raw partner, and actual ballot publication with a
statically equivalent full raw-partner successor in both voting directions.
Expected ready/blocked channels come directly from literal syntax. The historical
independent cryptographic, rejection, cyclic and policy controls remain intact.
No new randomized campaign over source Structural derivations is claimed.

Failures were proof engineering: readiness predicates needed explicit reduction
for a concrete decision; unused parallel-equivalence hypotheses polluted a local
induction; dependent phase domains required explicit whole-process cast identities;
and the Reachable alias needed a type annotation to select its swap theorem.
The statements and original model assumptions were retained.

Integrated evidence: `lake build` succeeds (4118 jobs); the clean targeted
control build succeeds (1468 jobs). The current full log contains 4899
standard-only nonempty and 103 axiom-free reports. The claims checker covers
3997 public theorem entries and 132 current-status documents. Seven changed Lean
oleans are current, and all 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Twenty-eight
public theorem audits, eight controls and two readiness-definition checks were
added. Log: `tmp/variable-overlap/source-raw-visible-full-build.log`.

Remaining B9/B10 acceptance obligations:

1. **Open — actual raw internal availability and source_reachable_internal_match.**
   For an enabled historical internal phase, construct an actual reduction or
   the required weak internal sequence from the related raw partner. Communication
   needs two compatible ready prefixes in that same raw state, including
   interleaved local scopes. A conditional additionally needs an actual ground
   guard before original thenBranch/elseBranch can apply. Current forward
   interpretation and conditional-location theorems do not supply this converse.
   The new visible readiness lemmas establish separate input/output existence,
   not a common communication redex or a valid conditional action.
2. **Open — integrate all clauses into one source relation.** Retain actual
   execution provenance, the shared reached phase/name coordinates, full frame
   presentations and complete handle bijections. The input and bound-output
   successor clauses are now checked in source_reachable_input_match and
   source_reachable_bound_match. Add internal closure and symmetric matching;
   retain old-handle output exclusion, rejection and freshness. B9 is complete
   only when these acceptance conditions all hold together.
3. **Open — source_reachable_weak_bisimulation and
   source_election_weak_bisimilar.** Assemble the source-level weak labelled
   bisimulation from the completed B9 relation, with actual Named.StaticEq
   observations and the original action semantics.
4. **Open — scopedVoterElection_ballot_secrecy.** Transfer to the actual scoped
   elections with documented freshness, arbitrary valid ground parameters and
   arbitrary finite administration size. Audit public hypotheses, full E/E0
   observations and independent controls. Do not assume the remaining
   correspondence or report stage matching/static equivalence as secrecy.

The retrospective reuse audit stays after B1–B10 secrecy completion.

Concrete next obstruction: SourceExtendedSyntax.Reduction.thenBranch and
elseBranch require a syntactically ground Formula embedded into the raw variable
context. A semantic realization of a ready branch does not itself satisfy that
constructor. The checked current frame presentation supplies actual provider
constraints, but a derivation must use them to ground the ready guard while
retaining its continuations and all providers. Compare that focused guard
rewrite with whole-live-code normalization before adding a larger layer. The
new visible proofs show that whole-live-code normalization was unnecessary for
input and output; no such premise was added. Internal communication separately
needs a simultaneous prefix-extraction argument. These are proof obligations,
not new attacker restrictions, source rules or supplied invariants.

The following checkpoint narratives are historical; their next-step prose is
superseded by the current dependency map above.


## Actual reachable source frame presentation

Status: **machine-checked, integrated and audited** for B9 reachable-state frame
reconstruction. B9 action matching and B10 remain open.

source_reachable_frame_presentation now gives every finite original execution
from scopedVoterElection a reached phase, refreshed name permutations, a complete
handle bijection and an actual RepresentsFrame witness at the exact phase policy
and full sourceView. Its premises are the actual execution, documented ns.Fresh,
left/right NoncesFreshFor and ch.Fresh. Candidate validity remains encoded by
CandidateSubstitution. There is no caller-supplied program class, target
presentation, model environment, elimination order or correspondence hypothesis.

The new fresh-output branch first derives actual CapturedEq congruence, including
selected occurrences and every SPK field. Its quotient environment satisfies the
extracted provider forest by its own retained provider equations. Quotient
exactness and BoundOutput.opened_algebra_values then yield an actual captured
structural equality with a derived ground term. captureCopy_structural preserves
any uniquely defined frame exporting the selected handle, including cyclic
payloads and nested locals; its recursive measure ignores payload size and is
preserved by the original binder renaming. CapturedEq.ground_reclose combines
this identity with the old actual reclosure. BoundOutput.opened_frame_presentation
returns the complete ground target under the exact outputHandle bijection.
BoundOutput.exists_frame_presentation recloses every name from an actual fresh
opening and normalizes its exact base/channel sets to an existential policy.
CoordinatedPhaseOpening.presented applies the already checked alignment theorem.
Named.Execution.election_presented_phase covers all original execution
constructors; the source theorem supplies its initial witnesses.

Fifteen controls cover retained providers, selective context holes versus
simultaneous substitution, the fourth SPK field, nontrivial quotient values,
cycles that cannot gain arbitrary ground captures, two dependent local binders,
a freshly opened private output and its independently expected value, copy
preservation of a cycle, full private policy reconstruction from an empty old
policy, rejection of that old empty policy as a target policy, and an actual
mixed historical run ending in replay rejection in either voting world.
No new randomized campaign over Structural is claimed. Universal proofs cover
constructors/contexts/finite executions; the directed controls test the stated
boundaries. The historical independent cryptographic controls remain imported.

Failures in this increment were proof engineering: a noncomputable simultaneous
substitution needed simplification before a concrete inequality could be decided;
recursive binder renaming needed an explicit varying type parameter and a
syntax-size termination proof; dependent policy indices required exposing the
frame representation during identity simplification. No candidate was weakened,
no source rule or cryptographic assumption was added, and both earlier checked
counterexamples remain decisive boundaries.

Integrated evidence: `lake build` succeeds (4113 jobs); the clean targeted
control build succeeds (1474 jobs). The current full log contains 4869
standard-only nonempty and 103 axiom-free reports. The claims checker covers
3969 public theorem entries and 132 current-status documents. Nine changed Lean
oleans are current, and all 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Forty-six
public theorem audits, fifteen controls and five definition checks were added.
Log: `tmp/variable-overlap/source-reachable-frame-presentation-full-build.log`.

Remaining B9/B10 acceptance obligations:

1. **Open — actual raw-partner action availability.** Given the maintained
   reachable source relation and a corresponding evaluated phase action, derive
   a real action (or the required internal weak sequence) from the other raw
   source state. The new frame presentation theorem supplies observations and
   provider equations; it does not reconstruct live code or supply an action.
   Inspect existing realization/interpretation and canonical action derivations
   for the precise missing converse before adding machinery.
2. **Open — source_reachable_internal_match, source_reachable_input_match and
   source_reachable_bound_match.** Use availability and existing phase matching
   to retain both actual successors in one relation. Preserve exact old/fresh
   handle domains, jointly refreshed private policies, unchanged public input
   recipes, output freshness, acceptance and stop-on-rejection behavior. The
   existing common-input result constructs a canonical partner action only.
3. **Open — source_reachable_weak_bisimulation and
   source_election_weak_bisimilar.** Assemble symmetric internal/free/bound action
   clauses and actual Named.StaticEq observations after B9 acceptance closes.
4. **Open — scopedVoterElection_ballot_secrecy.** Transfer the bisimulation to
   the actual scoped elections with documented freshness, arbitrary valid ground
   parameters and arbitrary finite administration size. Audit public hypotheses,
   full E/E0 observations and independently derived controls; no missing
   correspondence may become a final theorem premise.

The retrospective reuse audit remains after B1–B10 secrecy completion.

The following checkpoint narratives are historical; their next-step prose is
superseded by the current dependency map above.


## Derive actual output values in every equation algebra

Status: **machine-checked and integrated** for algebraic value extraction;
actual fresh-output frame presentation and B9/B10 remain open.
SourceFrameAlgebra's record requires evaluation to respect variables,
substitution and the original full EqE. Its Satisfies/Rigid predicates describe
frame solutions and hidden-value uniqueness in the chosen algebra. The existing
source predicates and actions are unchanged. Structural and BinderStructural
induction proves both preservation statements for every original constructor,
including active-active substitution, aliases, New-Par and binder exchange.

RepresentsFrame.opening_algebra_rigid uses the actual opening presentation;
BoundOutput.opened_value_unique uses actual old-frame reclosure. Neither accepts
ground-only rigidity or semantic realization equality as a reconstruction
premise. BoundOutput.opened_algebra_values extracts f and a ground m such that the
opened raw target satisfies the original ground constraints at the mapped old
frame and m. For every algebra M and every satisfying public environment/fresh
value, it derives all old-handle values as M.groundValue of that mapped frame and
the fresh value as M.groundValue m. The ground witness and old-value alignment
are derived, not caller-supplied. satisfies_of_ground maps original EqE-ground
solutions into any such model using its proved full-E laws.

SourceFrameAlgebraQuotient.ofTermCongruence builds a model from any term setoid
containing full E and respecting pointwise substitution into terms. This permits
a congruence relative to a fixed source frame; it does not require substituting
that frame's own variables in its assumptions. Evaluation uses Quotient.out,
and the laws prove independence from the chosen representatives. fullGround is
the concrete original full-E quotient. The intended congruence of actual fresh
capture structural paths is still unimplemented, so no source presentation is
claimed from the generic model result alone.

Eleven directed controls cover a real destructor equation, distinct ground names,
inhabited local aliases, dependent binder exchange, actual private output and its
fresh opening, rejected old spelling, a derived ground witness, retained old-zero
and fresh-one values with a nontrivial satisfying model, and the inhabited cyclic
local remaining non-rigid. No new randomized campaign is claimed. Failures were
proof engineering: explicit record parameters for recursive predicates, quotient
field binder elaboration and exact ground embeddings in a fixture. The final
proofs retain the candidate statements and original protocol assumptions.

Integrated evidence: `lake build` succeeds (4106 jobs); the clean targeted
control build succeeds (1408 jobs). The current full log contains 4820
standard-only nonempty and 101 axiom-free reports. The claims checker covers
3923 public theorem entries and 132 current-status documents. Five changed Lean
oleans are current, and all 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Forty public
theorem audits, eleven controls and seven definition checks were added. The
algebra/quotient definitions are proof instrumentation, with no new source rule,
execution relation or cryptographic assumption.
Log: `tmp/variable-overlap/source-frame-algebra-full-build.log`.

Remaining fresh-output work, all still **conjectured** unless stated checked:

1. Define Extended.CapturedEq by an actual Structural path between the same
   frame with a fresh active observer of two terms. Prove full-E inclusion,
   provider equations and congruence under term contexts. In particular, derive
   contextual congruence using actual local aliases; simultaneous Subst cannot
   simply be treated as rewriting one chosen occurrence.
2. Use the checked complete provider forest to instantiate the checked
   FrameAlgebra.ofTermCongruence constructor with CapturedEq. Derive its actual
   model solution from the provider equations and existing variable-prefix
   coordinates. Apply checked BoundOutput.opened_algebra_values and quotient
   exactness to obtain a captured-term Structural equality with the ground value.
3. Derive the fresh alias/copy and reclosure bridge that turns this equality,
   together with the actual old-frame reclosure path, into a complete target
   presentation. Reclose the actual full name prefix and preserve Option/
   outputHandle coordinates. Its private policy is existential at this step;
   the checked same-old-policy counterexample still forbids fixing it prematurely.
4. Finish Named.BoundOutput.exists_frame_presentation, then apply checked
   JointOpening.align_presentation to the full reached-phase witness and close
   source_reachable_frame_presentation. Actual raw-partner internal/input/bound
   matching and B10 bisimilarity/secrecy remain subsequent obligations.

The algebraic route avoids assuming an elimination order for the finite forest.
Its extra strength is derived from actual structural provenance. It does not
infer structural presentation from semantic equality or ground-only rigidity.
The actual capture congruence and reclosure bridges must still be proved; no
premise asserting either may enter the final secrecy theorem.

The following sections are earlier checked increments; their next-step prose is
superseded by the dependency map above.


## Complete provider extraction for every historical execution

Status: **machine-checked and integrated** for finite-forest extraction;
ground frame reconstruction and B9/B10 remain open.
SourceVariableFramePrefix uses LocalVars/closeVars as notation for finitely many
original newVar binders. FrameForest admits only nil and active definitions in
parallel. exists_variable_frame_prefix hoists every local in every original
frameOf, using original New-Par and parallel structural rules. It retains the
full active equations. localMap/closeVars_rename retain capture-avoiding
coordinates, outerVar_injective keeps public slots distinct, and
closeVars_exports identifies their exact embedded coordinates.

Named.exists_fresh_variable_frame_prefix extracts a fresh name opening from the
raw process, projects its actual frame, hoists locals, and recloses a full source
Structural path. Name allocation avoids both the requested context and every
literal name in the raw frame. The original UniqueDefinitions predicate requires
a definition for each restricted variable. closeVars_complete therefore derives
complete coverage of every local and public slot; Named.exists_complete_frame_prefix
retains this coverage and uniqueness. FrameForest.extract_provider exposes any
chosen full term and a remainder that does not define that variable, with an
actual structural path and every other equation retained.

BoundOutput.exists_complete_frame_prefix derives these properties for an actual
output using the old presentation. More strongly, SourceReachableFramePrefix's
Execution.complete_definitions derives them across every finite original action,
structural step and bijective reindexing. scopedVoterElection_execution_frame_prefix
starts at the actual scoped election with its documented parameter freshness:
it derives a reached phase, exact public-domain bijection, full JointOpening,
fresh name allocation and complete provider forest with an actual structural
frame path. It assumes neither current frame presentation nor supplied program
syntax. The forest may contain dependencies between local and public providers;
it is not a RepresentsFrame ground witness.

Seven controls cover two dependent locals with independently specified pair
values and public coordinates, extraction of the fresh provider, a retained
cyclic equation that still has no ground presentation, an actual private output,
and an actual historical execution through two publications, input and replay
rejection. No new randomized campaign is claimed. Proof-engineering corrections
concerned dependent existential syntax, namespace resolution, and explicit finite
Option case analysis in fixtures; no claim or protocol assumption was weakened.

Integrated evidence: `lake build` succeeds (4103 jobs); the clean targeted
control build succeeds (1461 jobs). The current full log contains 4773
standard-only nonempty and 101 axiom-free reports. The claims checker covers
3883 public theorem entries and 132 current-status documents. Five changed Lean
oleans are current, and 1684 local links resolve. No holes, custom axioms,
warnings or errors were found in scope; `git diff --check` passes. Twenty public
theorem audits, seven controls and five definition checks were added. The new
definitions describe variable-prefix notation and a frame-syntax predicate;
no operational rule or execution relation was added.
Log: `tmp/variable-overlap/source-variable-frame-prefix-full-build.log`.

The next missing proof is still Named.BoundOutput.exists_frame_presentation:
use actual current presentation and output provenance to eliminate the extracted
local provider system and produce some complete ground target presentation.
Finite-forest extraction now supplies syntax, freshness, unique providers and
all coordinates; it does not supply an elimination order or ground-valued
structural path. Neither unique definitions, local rigidity nor semantic
realization equality may be silently substituted for that proof. Once it is
constructed, checked JointOpening.align_presentation recovers the exact phase
policy and values. Then complete source_reachable_frame_presentation, actual
raw-partner internal/input/bound matching, and B10 bisimilarity/secrecy.

The following sections describe preceding checked increments; the frontier above
supersedes their descriptions of the next extraction step.


## Align an extracted frame with the reached phase

Status: **machine-checked and integrated** for alignment; constructive
fresh-output existence remains **conjectured**. In SourcePresentationAlignment,
RepresentsFrame.opening_presentation transports an actual frame structural path
through a chosen name opening and extracts an actual BinderStructural ground
frame. The assignment is extracted, not supplied, and may be noninjective.
SameRealizations.frame_structural_of_presentations compares full-E provider
values only after both actual opened presentations have been supplied.
JointOpening.frame_structural_of_presentations chooses openings fresh against
both complete frame name sets, reconstructs their structural path, and recloses
using Opens.structural_of_binder. JointOpening.align_presentation therefore
recovers the canonical state's exact policy and complete values from a joint
witness and any already constructed actual presentation of the other process.
It does not construct that latter presentation or establish action availability.

The five controls in SourcePresentationAlignmentSPOT cover an actual private
capture aligned from a larger unused base/channel policy, rejection of every
empty-policy target presentation, a full-E fst/provider rewrite, unequal public
bits rejecting the semantic premise, and the inhabited cyclic joint pair still
failing actual presentation. These literal expectations come from the original
capture and provider equations. No new randomized campaign is claimed. The only
proof-engineering correction was removal of an unused simp argument; no failed
semantic claim was replaced by a weaker theorem under the same name.

Integrated evidence: `lake build` succeeds (4100 jobs), including all five
new controls. The clean targeted control build succeeds (1403 jobs). The current
full log contains 4757 standard-only nonempty and 92 axiom-free reports; the
claims checker covers 3863 public theorem entries and 132 current-status
documents. Four changed Lean oleans are current, and all 1684 local links resolve.
No holes, custom axioms, warnings or errors were found in scope; `git diff
--check` passes. Twelve public theorem audits were added. No operational rule,
execution relation or cryptographic assumption was added.
Log: `tmp/variable-overlap/source-presentation-alignment-full-build.log`.

Next is Named.BoundOutput.exists_frame_presentation (planned): extract some full
actual target presentation from an actual output of a presented source. The
output's raw target must retain every old handle and the new None handle under
the outputHandle bijection. Private policy is existential during this extraction;
the full next-phase witness then supplies its exact historical policy through
checked alignment. Constructing dependent local-variable providers through
arbitrary structural scope movement remains the unresolved step. The existing
scoped-program/capture theorems remain conditional on supplied structural syntax;
they do not close this gap. B9 action matching and B10 still follow this work.


## Actual frame presentations through internal steps and input

Status: **machine-checked** branches of the reachable-presentation induction.
`SourceInputPresentationClosure.source_coordinated_internal_presented_next`
retains the actual target presentation and reached phase through the exact
handle cast. `source_coordinated_input_presented_next` retains actual raw target
and partner presentations at freshly composed base/channel coordinates, plus
the target phase witness, the partner's refreshed JointOpening and actual
Named.StaticEq between their unchanged observation frames. The partner has not
yet performed a matching input; the theorem does not claim a paired successor.

The input proof consumes actual current presentations, the intended induction
hypotheses. It derives every new freshness condition from common freshening.
`RepresentsFrame.transport_state_structure` uses the actual structural paths
already returned for whole canonical processes, then frame projection;
`JointOpening.common_fresh_input_presented` composes this with FreeStep.frameOf.
No semantic equivalence is promoted to a presentation. The mapped handle cast
helper preserves every full frame value and the actual restriction policy.

Five new input/internal controls cover a currently private literal that forces
key freshening, its rejected stale policy, actual historical input in both vote
worlds, actual replay rejection, and the rejected generic output shortcut.
Eight additional frame-compatibility controls prove that shortcut false: a
private atom absent from the old frame is captured by an actual fresh output.
The old frame and the reclosed target both admit empty private policy, but no
ground frame at that policy presents the target, regardless of channel policy
or chosen value. Keeping the process's private atom gives a full presentation.
This is a false generic claim/insufficient-invariant diagnosis, not a model
change or an attack on historical Helios. All controls are kernel checked;
there is no new randomized campaign.

Integrated evidence: `lake build` succeeds (4098 jobs); targeted controls
succeed (1458 jobs). The current log has 4745 standard-only nonempty and 92
axiom-free reports. The checker covers 3851 public theorem entries and 132
current-status documents. Five changed Lean oleans are current; 1684 local
links resolve. No holes, custom axioms, warnings or errors were found in scope;
`git diff --check` passes. This increment adds 18 public theorem audits,
including 13 controls, with no new operational rule or execution relation.
Log: `tmp/variable-overlap/source-input-presentation-full-build.log`.

Next: the fresh-output branch of source_reachable_frame_presentation, using
actual full process/phase provenance. Current frame presentation and reclosure
alone are insufficient. After that branch, construct actual raw-partner matches
with related successors and assemble source weak labelled bisimilarity/secrecy.


## Full execution from the actual scoped election

Status: **machine-checked, integrated and audited** phase correspondence for
every finite original Named.Execution from scopedVoterElection. Actual reachable
frame reconstruction and raw-partner matching remain open. This is not secrecy.

`SourceReachableElectionPhases.Named.Execution.election_phase` inducts on the
existing heterogeneous Execution, including structural paths, internal and free
actions, fresh bound outputs, bijective reindexing and arbitrary composition.
The conclusion gives a reached historical phase, base/channel permutations and
a bijection from the actual target variable type to that phase's entire handle
domain, with JointOpening to the complete mapped phase frame/body.

The input case invokes existing common freshening with the source paired with
itself; no other-world matching is claimed. It composes the refreshed private
name coordinates and retains the unchanged raw target. The output case combines
Option.map of the old handle bijection, outputHandle and the exact phase-domain
cast. Existing phase output exclusion rules out every old-handle FreeStep.

`scopedVoterElection_execution_phase` supplies the initial witness using the
checked scopedVoterElection_normalizes theorem, under Names.Fresh,
NoncesFreshFor for both parameters and Channels.Fresh. Its premises include only
actual execution and these documented initial conditions, not caller-supplied
program extraction or correspondence. `exists_scoped_execution_phase` uses the
existing allocator to prove Names/parameter freshness for arbitrary valid ground
candidate substitutions. One allocation works for both vote worlds, every
finite administration size and every fresh channel allocation.

`scopedVoterElection_execution_no_handle_output` excludes old-handle output from
all actual raw reachable states. SourceExecutionHandleRenaming provides exactly
the action transport needed for this Execution proof; it preserves full labels,
local binder exchange and fresh/old variable distinctions. No new execution
relation, operational rule, syntax or cryptographic equation is introduced.

Thirteen SourceReachableElectionSPOT controls include actual two-publication
execution from the scoped election, replay input followed by guard rejection,
blocked post-rejection input, explicit handle reindexing and full domain checks.
The private/public and inhabited cyclic reconstruction counterexamples remain.
The general induction covers arbitrary original derivations, not only these
canonical control runs. PBT gate: directed kernel controls and existing general
proofs; no new randomized campaign. Initial failures were proof engineering
(coercions, binder substitutions and decidable fixture elaboration).

Integrated evidence: `lake build` succeeds (4096 jobs); the targeted control
build succeeds (1454 jobs). The current full log contains 4727 standard-only
nonempty and 92 axiom-free reports. The checker covers 3833 public theorem
entries and 132 current-status documents. Five changed Lean oleans are current;
1683 local links resolve. No holes, custom axioms, warnings or errors were found
in scope; `git diff --check` passes. This increment adds 24 public theorem
audits, including 13 controls, and no new definition or operational rule.
Log: `tmp/variable-overlap/source-reachable-election-full-build.log`.

Next: derive actual full RepresentsFrame witnesses for these reachable targets,
including fresh outputs, then construct matching actions from the actual raw
partner with related successors. JointOpening still compares realizations;
neither it nor local rigidity is silently promoted to a structural presentation.
The existing blueprint contains the exact remaining declaration/dependency map.

## Full canonical coordinates

[SourceMappedCanonicalStates](../../ExplainableCrypto/Helios/Symbolic/SourceMappedCanonicalStates.lean)
defines `Named.mappedState hidden s e k`: both restriction policies and the
complete frame/body move together. Its identity theorem recovers restrictedState.
Its composition theorem is equality of the resulting actual Named processes,
so repeated freshening does not leave unresolved intermediate policy casts.
The theorem does not claim that arbitrary global renaming is Structural
conversion. Actual Structural freshening is supplied separately.

Full input-frame transport reflects a mapped visible input to the inverse
channel and recipe under the original frame, and maps that action back with
its exact literal label. Every constructor and all SPK fields are retained.

[SourceCoordinatedPhases](../../ExplainableCrypto/Helios/Symbolic/SourceCoordinatedPhases.lean)
defines `CoordinatedPhaseOpening` with explicit base/channel permutations,
actual phase and raw process, plus equality of raw and phase handle domains.
The same witnesses can be supplied to both vote worlds. The relation holds
canonically, survives all Structural changes, contains the previous identity-
coordinate PhaseJointOpening and retains actual free channel support.

## Input classification and both-world freshening

[SourceCoordinatedInput](../../ExplainableCrypto/Helios/Symbolic/SourceCoordinatedInput.lean)
proves `source_coordinated_public_input_next`. A recipe Public under the current
mapped policy reflects to a Public recipe under the original policy. Exhaustive
source input correspondence identifies the waiting input phase, voter channel
and typed three-handle recipe. The result contains the actual stage input Step
to check and CoordinatedPhaseOpening of the unchanged raw target at that phase.
Deterministic full target closure chooses the complete canonical check body;
acceptance remains a later internal transition.

[SourceCoordinatedFreshInput](../../ExplainableCrypto/Helios/Symbolic/SourceCoordinatedFreshInput.lean)
proves `source_coordinated_common_input_next` for arbitrary actual raw inputs.
It starts from both raw source joint relations in common current coordinates
and a reached phase. Both mapped canonical partners freshen together. Composing
the old and new permutations gives the coordinates used for the inverse input
recipe, check phase and raw target. Both raw source relations and full old-frame
StaticEq survive in those same coordinates. The next phase is reached.

The theorem also constructs an actual same-label Named input from the other
fresh canonical partner to a target with CoordinatedPhaseOpening at the same
check phase. It does not construct that action from the arbitrary raw partner
that is merely related to the canonical one. This remaining converse is an
explicit boundary of the theorem, not an assumed reconstruction callback.

## Subsequent transitions

[SourceCoordinatedInternal](../../ExplainableCrypto/Helios/Symbolic/SourceCoordinatedInternal.lean)
reflects actual raw internal actions to original residual Tau, identifies the
next stage and preserves the same coordinates. Exact handle equality and HEq
of full original canonical states transport the raw target. The phase relation
is preserved along every finite raw internal trace from a reached phase;
private-channel publicness is expressed under the current mapped policy.

[SourceCoordinatedOutput](../../ExplainableCrypto/Helios/Symbolic/SourceCoordinatedOutput.lean)
reflects actual raw bound output to the full original Publication, then retains
the current coordinates at the next phase after fresh-handle renaming. The
literal channel is k(ch.broadcast). Old values, the complete new message,
all continuations and both restriction policies remain in the target relation.
The required determinism is discharged with the election residual theorems.

## Controls and verification

[SourceCoordinatedSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceCoordinatedSPOT.lean)
has 20 public kernel controls. Nonidentity coordinates move the secret key to
100 and the trustee channel to 200; a second mapping tests composition order.
The old secret literal is private under the original policy and public under
the current policy, with exact inverse recipe name 100. An actual election input
reaches check; both vote worlds refresh and admit the same canonical input.
A real subsequent internal step and arbitrary finite internal traces retain
the current coordinates. Private trustee output remains blocked, and actual
first publication retains the full phase relation on the enlarged domain.
The stale-policy stage input and reversed composition are rejected. Full
fourth-field input support remains explicit.

The internal fixture constructs a real accept-or-reject transition and does
not assert that this literal input is accepted. Inputs and acceptance are
separate source events. Expected names, labels, composition and phase fixtures
are independently specified. The gate uses directed kernel controls and general
proofs, with no new random cryptographic campaign or security inference from
failed search. Historical In/Scope/alpha and receive/check separation supply
the model reference. Full E/E0 and original observations remain unchanged.

Integrated verification: `lake build` passes **4060 jobs**. The log reports
**4434** nonempty standard-only and **91** axiom-free results. The claim audit
covers **3539** public theorem entries and **123** current-status documents.
All nine changed Lean sources have current oleans; **1578** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **37** theorem audits,
including **20** public kernel controls, and two proof definitions.
The targeted control build passes **1431 jobs**.
Build log: `tmp/variable-overlap/source-coordinated-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-coordinated-verification.txt`.

Remaining: action construction in arbitrary related raw counterparts,
existing-handle free-output closure, raw output-frame Structural presentation,
and assembling the final two-world weak labelled bisimulation/secrecy theorem.
No JointOpening transitivity or raw StaticEq from semantic target equality is
assumed. See the [blueprint](helios-proof-blueprint.md),
[results ledger](helios-results.md) and [task list.md](../../task%20list.md).
