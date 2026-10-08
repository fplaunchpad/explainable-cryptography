# Independent source-frame compatibility

## Output-policy reconstruction boundary

Status: **refuted** for the generic claim that a current frame presentation and
actual output reclosure always yield a target presentation at the same base
policy. SourceFrameCompatibilitySPOT now retains a live output of private atom
40 whose old empty frame admits both empty and {40} policies. Its actual output
and reclosure are checked. The fresh target has a full {40} presentation, but
has no empty-policy presentation for any ground value or hidden-channel set.
Two distinct atom assignments prove the latter universally over candidate
frames. This counterexample concerns private-name policy, not nonunique local
variables or empty realization classes. The original operational rules remain.

The reachable-election proof must retain its full process/phase provenance.
Actual internal/input presentation closure uses actual whole-state structural
paths and is recorded in [coordinated phases](helios-source-coordinated-phases.md).
It does not assume the false output shortcut. The inhabited cyclic semantic
counterexample remains independently retained.

Status: machine-checked. Independent common-policy presentations of the same
Named source frame agree on every public full-E equality test.
`Named.StaticEq.trans` now composes arbitrary existing static-equivalence
witnesses. The proof uses the previous common-policy construction and discharges
its missing middle-frame comparison. No presentation-compatibility premise
remains in transitivity.

B9/B10 remain incomplete at 8/10 unweighted milestones. Canonical environment/body
correspondence for arbitrary source action paths, remaining admissibility/action
matching and the final weak labelled bisimilarity/symbolic secrecy theorem are
still open. Follow the [blueprint](helios-proof-blueprint.md) and
[single backlog](../../task%20list.md).

## Constraint interpretation

`Extended.Satisfies` records the equations imposed by active definitions.
Plain processes contribute True, parallel composition conjoins constraints,
and variable restriction existentially quantifies a complete ground term.
`frame_constraints_realizes_iff` proves exact agreement with the existing
interpretation of the extracted frame. Thus all Extended structural rules
preserve these constraints, including both active-substitution cases.

`Named.Models` additionally takes an assignment from base-name literals to
atoms. Restricting a base name existentially changes its assigned atom inside
the binder. Channel restriction contributes no frame equation. Assignments may
collide: this relation is proof instrumentation, not an attacker deduction
relation or an operational model of freshly generated protocol names.

`Named.Structural.models` proves invariance under every current source structural
rule, including name extrusion, base/channel alpha conversion, both kinds of
scope commutation, active substitution and full-E rewriting. The proof checks
the original free/all-name side conditions. `models_names_congr` depends only
on free base names, and `models_mapNames` transports source syntax by actual
permutations. Arbitrary assignment functions inside Models are not mistaken
for reflecting name permutations.

## Exact observations and composition

`ValidEquation a r s` requires `r =E s` under **every** environment satisfying
the frame constraints of `a`. The universal quantifier is essential. Two
different private atoms may coincide in one solution, while their equality is
false in the identity solution.

For a canonical ground frame, `canonicalFrame_models_iff` identifies precisely
the assignments that fix every unbound name, with every exported value retained
modulo full E. The identity assignment supplies a solution.
`canonicalFrame_validEquation_iff` then proves that universal validity is exactly
the frame's original recipe equality for public recipes. Forward preservation
of E under arbitrary name maps proves one direction; the identity solution
proves the other. It never assumes that a noninjective map reflects E.

| Public interface | Checked scope |
| --- | --- |
| `RepresentsFrame.models` | Every actual ground presentation supplies a solution. |
| `RepresentsFrame.validEquation_iff` | Exact full-E equality observations through the entire source presentation path. |
| `RepresentsFrame.compatible` | Independent presentations of one source frame, under the same base policy and possibly different hidden channel policies, are Frame.StaticEq. |
| `canonicalFrame_structural_staticEq` | Actual structural equivalence of canonical restricted frames implies full static equivalence. |
| `Named.StaticEq.trans` | Arbitrary two static witnesses compose, using common-policy alignment and the proved middle-frame compatibility. |
| `StaticEq.validEquation` | All unchanged literal recipe tests transfer after freshening actual witnesses around them. |
| `staticEq_iff_validEquations` | Exact observation characterization when actual common-policy ground presentations are supplied. |

The last premise matters. Inconsistent raw constraints make every universal
equation vacuously valid, and such a frame has no ground presentation.
The characterization does not infer a static witness for arbitrary raw syntax.

## Action interfaces and controls

Actual Named reductions and free actions preserve the full solution relation
and all valid equations, through the existing frame-projection theorems.
Bound output preserves the reclosed solution relation. `validEquation_newVar_iff`
and `BoundOutput.old_validEquation_iff` give exact preservation of equations over
old handles after shifting them past the new output handle. The new handle may
support additional equations. These frame results do not establish behavior
matching for executable bodies.

Twenty-three kernel controls include an identity solution, an intentionally
colliding private assignment, distinct/shared handle observations, alpha-renamed
binders with the same full solutions, private-versus-free literal comparisons,
inconsistent constraints and the necessity of presentation witnesses, dependent
active lets, wrong exports, a full fourth proof field, public zero/one separation,
three-frame composition, complete literal tests, a reached protocol transcript,
and an actual bound publication retaining old equations while adding a distinct
new handle. Public zero versus one is rejected for arbitrary Named static
witnesses, beyond rejection of just one proposed frame certificate.

Reality oracle: Cortier–Smyth Definition 1 and Figure 3. The constraint layer is
new proof instrumentation; its canonical observation iff and full structural
invariance justify its use for this result. Existing full E, source syntax,
actions, public observations and cryptographic fields are unchanged. The gate
uses general structural proofs and directed kernel controls. No new randomized
cryptographic campaign or inference from failed search is claimed.

Integrated verification: `lake build` passes **3973 jobs**. The log reports
**3857** nonempty standard-only and **72** axiom-free results. The claim audit
covers **2943** public theorem entries and **110** current-status documents.
All nine changed Lean sources have current oleans; **1388** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **62** theorem audits,
including **23** public kernel controls, and checks all three new constraint/
observation definitions. The targeted control build passes **1313 jobs**.
Build log: `tmp/variable-overlap/source-frame-compatibility-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-frame-compatibility-verification.txt`.

## Artifacts

The implementation is in
[SourceFrameConstraints](../../ExplainableCrypto/Helios/Symbolic/SourceFrameConstraints.lean),
[SourceNamedFrameSolutions](../../ExplainableCrypto/Helios/Symbolic/SourceNamedFrameSolutions.lean),
[SourceFrameSolutionStructure](../../ExplainableCrypto/Helios/Symbolic/SourceFrameSolutionStructure.lean),
[SourceCanonicalFrameSolutions](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalFrameSolutions.lean),
[SourceIndependentFrameCompatibility](../../ExplainableCrypto/Helios/Symbolic/SourceIndependentFrameCompatibility.lean),
[SourceFrameEquationActions](../../ExplainableCrypto/Helios/Symbolic/SourceFrameEquationActions.lean)
and [SourceFrameCompatibilitySPOT](../../ExplainableCrypto/Helios/Symbolic/SourceFrameCompatibilitySPOT.lean).
Public declarations have type/axiom entries in
[Audit](../../ExplainableCrypto/Helios/Symbolic/Audit.lean).
The [results ledger](helios-results.md) retains the enquiry and evidence record.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.

[Full Named visible interpretation](helios-source-named-visible.md) now supplies
the previously separate canonical-to-prenex visible connection for every actual
free/bound action, retaining full target interpretation. Finite-support
faithfulness is sufficient for Extended internal transport, but fixed old
environment injectivity is refuted by an alpha/dead-field control. General Named
internal correspondence, required new-frame presentation/relation invariants
and final source bisimilarity/secrecy remain open.
