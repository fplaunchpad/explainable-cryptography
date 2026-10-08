# Variable domains and admissibility of named source processes

Current update: [local rigidity](helios-source-local-rigidity.md) refutes the
Extended normalization implication from WellFormed/nonempty full class alone.
The counterexample also has an embedded joint opening; Named.Structural
separation and a sufficient reconstruction invariant remain open.

B9 now tracks exported handles and unique active definitions for every current
Named process. All structural rules and internal/free actions preserve these
invariants. Bound output keeps exactly the old exported domain under Some; the
source has unique definitions exactly when the target does and defines its new
output variable. Canonical election states and their raw targets have closed
variables and unique definitions. Their factored Extended action bodies now
have these properties too. These are machine-checked variable conditions;
general Named equality observations and canonical environment/body correspondence
remain open. B9/B10 stay at 8/10 milestones (80%, unweighted).

## Exported domains and unique definitions

[SourceNamedExports](../../ExplainableCrypto/Helios/Symbolic/SourceNamedExports.lean)
defines the domain of a Named frame recursively. Name restrictions leave the
variable domain unchanged; a variable restriction hides None. Projection keeps
the domain, name maps keep it, and variable maps yield exactly its image. A
shift through Some never defines the fresh None. `Structural.exports` covers
every existing rule, including alpha and binder exchange.

[SourceNamedUniqueDefinitions](../../ExplainableCrypto/Helios/Symbolic/SourceNamedUniqueDefinitions.lean)
defines at most one active definition per exported variable, with a required
definition beneath every variable restriction. It proves preservation and
reflection by injective variable maps, arbitrary base/channel maps, name
prefixes and frame extraction. Equal payloads may inhabit distinct handles;
name restriction does not make two definitions of one variable distinct.

[SourceNamedUniqueStructure](../../ExplainableCrypto/Helios/Symbolic/SourceNamedUniqueStructure.lean)
proves `Structural.uniqueDefinitions` for every constructor. Name/variable
extrusion preserves separation of parallel definitions. Exchanging two variable
binders exchanges their required definitions. Alpha never changes the variable
domain or its multiplicity.

## Actions reuse complete frame preservation

[SourceNamedDomainActions](../../ExplainableCrypto/Helios/Symbolic/SourceNamedDomainActions.lean)
derives internal/free domain and uniqueness invariants from the checked frame
projection and structural transport. Bound-output reclosure yields
`BoundOutput.old_exports`, preserving each old variable exactly, without a
well-formedness premise. `BoundOutput.uniqueDefinitions_iff` states:

```text
source.UniqueDefinitions ↔ target.UniqueDefinitions ∧ target.Exports none
```

The forward consequences supply target uniqueness, the fresh export and full
target-domain coverage when the original domain was complete. The iff does not
assert that arbitrary raw output syntax has a defining active substitution:
source uniqueness is the load-bearing premise for that consequence.

## Closed variables and free-label scope

[SourceNamedVariableClosure](../../ExplainableCrypto/Helios/Symbolic/SourceNamedVariableClosure.lean)
defines full variable occurrence checks, `Closed`, and `WellFormed` as unique
definitions plus variable closedness. Checks include every active payload field
and every plain continuation. Complete exported-domain coverage implies
closedness and is preserved by all current action kinds. Actual
`restrictedState` values supply uniqueness and complete coverage, so their
arbitrary structural, internal, free and bound-output targets are well-formed.
No reachability premise or conditional closedness callback is required for
these canonical-state results.

These definitions do not assert acyclicity or all possible source-admissibility
conditions. The earlier nonclosed raw Rewrite counterexample remains valid:
an unused ambient variable can be inserted into a discarded projection field.
It is complete domain coverage, supplied by canonical states, that discharges
closedness for their arbitrary representatives.

[SourceNamedLabelScope](../../ExplainableCrypto/Helios/Symbolic/SourceNamedLabelScope.lean)
defines `LabelScoped` as the free-variable condition `fv(label) ⊆ dom(frame)`.
Full input recipes and free-output handles are checked. Structural and internal/
free actions preserve that condition for every fixed label. After bound output,
shifting an old label through Some preserves and reflects its scope. Canonical
states and enlarged output targets cover all labels over their variable types.
This does not discharge name freshness or make a private literal public under
an old fixed name policy; those remain separate conditions.

## Well-formed factored action bodies

[SourceAdmissiblePrenex](../../ExplainableCrypto/Helios/Symbolic/SourceAdmissiblePrenex.lean)
transfers complete domain coverage and uniqueness from a Named source through
any structural path to an outer name prefix and Extended body. All three
`prenex_wellFormed` results retain actual Extended actions, structural paths
from both endpoints, and well-formed bodies with complete exported domains.
Free actions keep the exact original label, its prefix freshness and its
variable-scope proof. Bound output retains the channel, the enlarged target
type and all old/new definitions. These results establish the variable part of
admissibility for the existing factorizations. They do not choose satisfying
environments or identify canonical process bodies across alpha.

## Controls and remaining work

[SourceNamedAdmissibilitySPOT](../../ExplainableCrypto/Helios/Symbolic/SourceNamedAdmissibilitySPOT.lean)
contains sixteen public kernel controls. They reject duplicate definitions
across private name scopes, allow equal values under distinct handles, retain a
raw output lacking a local definition, and accept ordinary input binders
without active aliases. A fourth-field undefined label variable is rejected;
the same recipe becomes scoped when that handle is defined. The Named raw
Rewrite closedness boundary and alpha domain/uniqueness transport are retained.
Actual restricted publication has a well-formed target, separate old/fresh
exports, shifted old-label scope, and scoped future recipes using the new
handle. Full-domain factorization is checked for actual bound publication,
private communication and the retained alpha-input transition.

The reality oracle is Section 5.1's active-definition, frame-domain and closed
variable conditions and Definition 2's free-label domain premise. These are
structural kernel proofs and independent controls, with no new randomized
cryptographic campaign or security inference from search failure. No existing
source rule, E equation or public observation changes.

The subsequent [Named static witness record](helios-source-named-static.md)
now supplies common restricted-substitution presentations and full equality
certificates at reached source stages. Next: canonical-presentation compatibility/
reflection and environment/body correspondence through structural and alpha
representatives; outer voter
nonce/let syntax; source weak labelled bisimilarity and symbolic secrecy.
See the [blueprint](helios-proof-blueprint.md),
[frame projection](helios-source-frame-projection.md),
[action factorization](helios-source-bound-prenex.md), and
[task list](../../task%20list.md).

Integrated verification for the Named variable-admissibility checkpoint: `lake build` passes **3910 jobs**, with
**3353** nonempty standard-only and **57** axiom-free reports. The claim audit
covers **2424** public theorem entries and **99** current-status documents.
All ten changed Lean sources have current oleans; **1235** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-named-admissibility-full-build.log`.
This increment adds 69 theorem audits, including sixteen public kernel controls.
Targeted controls pass 1292 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-named-admissibility-verification.txt`.
