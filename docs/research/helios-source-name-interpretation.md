# Name-equivariant interpretation and Named prenex representatives

Current internal frontier: [general Named communication and actual election
matching](helios-source-communication.md) are now checked without injectivity.
Arbitrary Named conditional correspondence, required target presentation/relation
invariants and final secrecy remain open. Earlier open internal statements below
describe their checkpoint; B9/B10 are still incomplete.

B9 now transports the checked Extended interpretation under consistent name
renaming and reflects it under bijections. Every current finite Named process
also has a structurally equivalent outer name prefix and a single Extended
body. That prefix can be distinct and avoid any finite set. These results
prepare the Named correspondence; they do not yet interpret arbitrary Named
structural/operational paths or establish canonical active-frame targets.
B9/B10 remain open at 8/10 milestones (80%, unweighted, not an effort estimate).

## Consistent environments

[SourceEquationalNameTransport](../../ExplainableCrypto/Helios/Symbolic/SourceEquationalNameTransport.lean)
transports Formula/Agent full-E congruence and EvalEq under arbitrary base/channel
maps. Bijections reflect these relations. Environment extension commutes with
the same base map on every old value and the fresh emitted message. Variable
indices and binder roles do not change when either name sort is renamed.

[SourceInterpretationNames](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretationNames.lean)
proves `Realizes.mapNames`: the Extended source, complete ground environment
and interpreted body move together. Active equations use full E-substitution
commutation; restricted variables choose the mapped old witness. Arbitrary maps
suffice for this forward implication. Actual base/channel bijections give an
iff and recover an arbitrary target environment/body through inverse maps.
The theorem does not assert that arbitrary maps preserve negative guard truth
or reflect operational behavior.

[SourceInterpretedNameActions](../../ExplainableCrypto/Helios/Symbolic/SourceInterpretedNameActions.lean)
preserves and reflects the interpreted free-label relation with consistent
source label, environment and process maps. Input remains exactly the evaluated
mapped recipe. Output retains the complete E-related environment value.
Raw captured-target realization commutes with the same map on the actual
emitted message and every old value, and bijections reflect that statement.

[SourceFreshInterpretation](../../ExplainableCrypto/Helios/Symbolic/SourceFreshInterpretation.lean)
connects actual frame/process states. Full mapped frames realize their mapped
bodies, and the general reflection theorem applies to arbitrary complete
frame environments. The existing common fresh-policy construction now also
retains realizations of both actual worlds, alongside structural correspondence,
publicness of the unchanged input recipe, its fixed public channel and complete
two-world Frame.StaticEq. This is an interface for source representatives, not
an interpretation theorem for all Named structural derivations.

## Moving name restrictions to an outer prefix

[SourceNamePrefixStructure](../../ExplainableCrypto/Helios/Symbolic/SourceNamePrefixStructure.lean)
derives extrusion across a name prefix with freshness for every binder. It
handles both parallel directions, commutes an enclosing variable restriction
with the prefix, composes prefixes and freshens a prefix with one coherent
base/channel permutation on its entire Extended body.

[SourceNamedPrenex](../../ExplainableCrypto/Helios/Symbolic/SourceNamedPrenex.lean)
proves `Named.exists_prenex` for every current finite Named constructor.
Name restrictions become an outer list; all active substitutions, plain
processes and variable restrictions remain in one Extended body. In a parallel
case, the left prefix is first freshened away from all names in the original
right component, so its extrusion cannot capture that component. The right
prefix is then freshened away from the left Extended body's free names before
its own extrusion. Both transformations use existing alpha/context rules.
Variable restrictions commute past the name prefix via Name-Var-Comm and
return to the Extended representation via Embed-Var.

`exists_fresh_prenex` additionally avoids any finite external name set.
`exists_distinct_fresh_prenex` supplies a distinct prefix as well. This is a
structural representative theorem. It does not remove or solve active
constraints, choose their ground environment, normalize an entire operational
derivation, or assert the Extended body is already a canonical frameProcess.
No source structural constructor or operational rule was added or weakened.

## Controls and remaining work

[SourceNameInterpretationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceNameInterpretationSPOT.lean)
contains thirteen kernel controls. An actual alpha binding has a moved
environment; retaining its stale environment is rejected. Name/channel
collapsing maps cannot justify reflection. A renamed input keeps its exact
message and receiver; capture environments commute, and the old key and all
four proof fields move consistently. Inverse capture transport and fresh
actual reached election states retain full interpretation and observations.

A concrete prenex extrusion first renames a private receiver channel so the
other sender stays public. The unfresh extrusion is rejected by the independently
checked invariant of free channels. A mixed name/variable/parallel context has
a distinct fresh prenex representative. These are kernel controls and general
structural proofs, not a new randomized cryptographic campaign or an inference
of security from unsuccessful attack search.

The subsequent [operational factorization](helios-source-operational-prenex.md)
now covers all current Named internal/free actions under common prefixes, with
exact labels and converse reconstruction. Next factor bound outputs and use
consistent environments to connect these representations to canonical states.
Establish canonical active-frame/continuation correspondence, general named
observations/admissibility and outer voter nonce/let syntax, then source weak
labelled bisimilarity and symbolic secrecy. General replication, mobile
channels and name creation under arbitrary plain prefixes remain outside the
current finite historical syntax.

See the [blueprint](helios-proof-blueprint.md),
[visible interpretation](helios-source-visible-interpretation.md),
[fresh policies](helios-source-fresh-names.md),
[name restrictions](helios-source-name-restrictions.md) and
[task list](../../task%20list.md).

Integrated verification for the name-interpretation/prenex checkpoint: `lake build` passes **3883 jobs**, with
**3194** nonempty standard-only and **48** axiom-free reports. The claim audit
covers **2256** public theorem entries and **95** current-status documents.
All nine changed Lean sources have current oleans; **1182** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-name-interpretation-full-build.log`.
This increment adds 38 theorem audits, including thirteen kernel controls.
Targeted controls pass 1265 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-name-interpretation-verification.txt`.

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
