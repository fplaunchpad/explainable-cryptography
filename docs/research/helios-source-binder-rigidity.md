# Binder rigidity and actual frame presentations

Current follow-up: [recipe capture reconstruction](helios-source-recipe-capture.md)
now gives full provider-context substitution and actual ground presentations
for explicit fresh recipe-valued captures. Extracting that form from arbitrary
reachable representatives, and final secrecy, remain open.

Current follow-up: [Named execution rigidity](helios-source-rigid-execution.md)
now preserves the necessary invariant through all original Named actions and
finite executions with bijective handle reindexing. The cyclic joint family is
excluded from executions starting at canonical election states. Sufficient
reachable reconstruction and full secrecy remain unproved.

Status: **machine-checked** structural opening witnesses, binder/bound-output
rigidity and the full Named frame-presentation boundary. B9/B10 remain at 8/10
unweighted milestones (80%); symbolic secrecy remains unproved.

The earlier [local-rigidity counterexample](helios-source-local-rigidity.md)
now survives every original Named structural rule. More strongly, the cyclic
semantic partner beside any complete frame/body admits no complete ground frame
presentation under any hidden-name policy or frame values on that handle domain.
It therefore has no partner in the current presentable-frame `Named.StaticEq`
relation, even though its full `JointOpening` partner remains inhabited.

## Structural witnesses and preservation

`SourceRigidityEnvironment` proves that Satisfies and Rigid depend only on
full-E environment classes. `rigid_newVar_body` gives rigidity at every chosen
local value; inconsistent choices remain vacuously rigid. `SourceRigidityBinders`
proves `rigid_varComm`: swapping two local binders with the required renaming
preserves rigidity. The proof transports dependent constraints between
E-equivalent environments; it does not replace E-equality with literal equality.

`SourceBinderStructure` defines `Extended.BinderStructural`, a comparison built
from original Extended.Structural paths, parallel/restriction congruence and
variable commutation already present in Named.Structural. `BinderStructural.named`
turns every comparison into an actual Named structural path between embedded
endpoints. It also preserves SameRealizations, Satisfies and Rigid. No source
transition or Extended.Structural constructor is added.

The existing `Named.OpeningTransport` and `OpeningEquivalent` are strengthened
in place to return BinderStructural bodies. The original rule induction still
handles alpha, name extrusion, mixed binder exchange and unused restrictions.
`Structural.transport_binder_opening` exposes the stronger witness.
`Structural.transport_opening` retains its former SameRealizations interface
by deriving it from that witness. No duplicate opening proof implementation is
introduced.

`SourceBoundRigidity` proves actual Extended bound-output frame reclosure with
BinderStructural. Consequently `BoundOutput.rigid_reclose` is an equivalence
between the source and the target with its exported variable hidden again.
`rigid_target` and `rigid_all_targets` preserve all remaining local choices in
arbitrary target environments. The converse is false: exporting an unconstrained
local can remove its uniqueness obligation from the target. Reclosure retains
that obligation exactly.

## Full Named boundary

`SourceNamedRigidityBoundary` proves `Structural.binder_of_embeds` and
`structural_embeds_iff_binder`. Thus arbitrary name-scoped structural detours
between embedded endpoints introduce no additional body comparison beyond
BinderStructural. `Structural.rigid_embeds` gives full Named rigidity preservation
between those endpoints, and the cyclic family is proved non-Structural there.

`SourcePresentationRigidity` gives the stronger observation boundary:

- `Opens.frameOf` retains the exact chosen allocation while dropping plain code.
- `Opens.canonicalFrame_rigid` holds for any assignment and actual allocation,
  without a freshness or injectivity premise on those assignments.
- `RepresentsFrame.opening_rigid` forces every chosen opening of a presentable
  raw process to be rigid in every environment.
- `frame_with_unconstrained_local_no_presentation` quantifies over all target
  ground frame values, restricted-name policies and hidden channels.
- `frame_with_unconstrained_local_no_staticEq` excludes every partner in the
  current ground-presentable Named.StaticEq relation.

This rules out obtaining the final observation clause from JointOpening alone.
It does not show that the cyclic process is reachable from the election, refute
protocol secrecy, or refute raw action matching. The static relation deliberately
carries actual frame presentations; nonpresentable syntax need not relate to
itself under that definition.

## Controls and evidence

`SourceBoundRigiditySPOT` has seventeen public kernel controls. Dependent local
values 40 and pair(40,41) remain correctly coordinated after binder exchange.
An actual output through a local restriction preserves rigidity for every
complete target environment; swapping the independently fixed local/capture
values incorrectly is rejected. A real output of an unconstrained local gives
a rigid target but a non-rigid source, refuting converse preservation. Full Named
normalization and arbitrary frame-presentation attempts fail for the cyclic
joint pair, while an actual canonical state retains its static observation
witness. Earlier opening-comparison controls are rechecked under the stronger
definition.

The reality oracle is the original variable-commutation, Open-Atom and Scope
rules plus the actual frame-presentation requirement in Definition 1. Full E/E0,
all SPK fields, structured-key E5, full-ciphertext E6 and explicit public
observations remain unchanged. These are general rule proofs and directed
kernel controls; no new randomized cryptographic campaign is claimed.

Integrated verification: `lake build` passes **4078 jobs**; the targeted controls
pass **1370 jobs**. The current log reports **4546** nonempty standard-only and
**91** axiom-free results. The claim audit covers **3651** public theorem entries
and **127** current-status documents. All fourteen changed Lean sources have
current oleans; **1627** local links resolve. No proof holes, custom axioms,
warnings or errors were found in the checked scope; `git diff --check` passes.
This increment adds **42** theorem audits, including **17** public kernel
controls, and one auxiliary comparison definition. Existing opening comparisons
are strengthened in place; the previous semantic transport interface and its
avoidance control remain checked.
Log: `tmp/variable-overlap/source-binder-rigidity-full-build.log`.

## Next proof obligation

Retain enough reachable structural/frame information to prove normalization and
construct matching actions in arbitrary raw counterparts. Rigidity is necessary;
sufficiency remains unproved. The new opening witness and bound-output reclosure
are tools for this proof, not assumed reconstruction callbacks. A full maintained
Named action invariant still needs integration with the election relation.
Complete raw bound-output frame presentation, then the paired weak labelled
bisimulation and secrecy theorem. The existing-handle election case remains
closed by [publication separation](helios-source-publication-separation.md).

See the [blueprint](helios-proof-blueprint.md),
[task list](../../task%20list.md) and [results ledger](helios-results.md).
