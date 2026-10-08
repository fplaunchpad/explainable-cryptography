# Static-equivalence witnesses for named source frames

Current update: [binder rigidity](helios-source-binder-rigidity.md) now proves
full Named.Structural separation of the cyclic joint pair and excludes all its
ground frame presentations/StaticEq partners. Structural opening comparison is
stronger, and Extended bound-output rigidity is checked. Earlier statements
leaving these facts open below are historical; reconstruction sufficiency remains open.

B9 now supplies Definition 1's common restricted-substitution witnesses at the
Named source layer. Every reachable election stage inherits the complete B7/B8
frame-equivalence result, including arbitrary structural representatives.
Witnesses retain actual structural paths from both extracted frames and full
all-public-recipe equality observations. Coherent alpha conversion freshens
both presentations away from arbitrary fixed recipe tests. These results check
the static clause; matching arbitrary Named actions and the final secrecy
theorem remain open. B9/B10 stay at 8/10 milestones (80%, unweighted).

## Actual frame presentations

[SourceNamedFramePresentation](../../ExplainableCrypto/Helios/Symbolic/SourceNamedFramePresentation.lean)
defines `canonicalFrame hidden φ` as the complete active substitutions under
explicit base/channel name restrictions. `RepresentsFrame a hidden φ` requires
a Named Structural path from `a.frameOf` to that canonical frame. It preserves
the original complete frame rather than selecting only an output tally.
Canonical restricted states supply this path through the checked frame-extraction
bridge. Every supplied presentation implies full domain coverage and variable
well-formedness.

Structural, internal and free actions transport these presentations. After a
bound output, the same presentation is recovered when the fresh output handle
is restricted again. This reclosure result does not discard the newly public
handle when comparing unrestricted targets.

## Common witnesses and all equality observations

[SourceNamedStaticEquivalence](../../ExplainableCrypto/Helios/Symbolic/SourceNamedStaticEquivalence.lean)
defines `Named.StaticEq a b` with existential common base/channel policies and
two complete frames. Both source presentation paths and `Frame.StaticEq` are
required. The latter quantifies over all public recipes and full E equality,
including nested uses of every retained proof/ciphertext/partial/result field.

The relation has checked symmetry, reflexivity for supplied frame presentations,
and preservation/reflection through arbitrary structural paths. Internal and
free actions on either side preserve its static witness. Every witness implies
both processes have the complete handle domain and are variable-well-formed.
`restrictedState_staticEq_of_frames` connects actual canonical Named states to
the existing full-frame criterion.

The current definition covers complete finite ground-presentable frames over
`Fin handles`. It does not assert that every syntactically well-formed raw frame
has such a presentation. [Independent frame compatibility](helios-source-frame-compatibility.md)
now proves compatible public equality tests for unrelated presentations and
Named.StaticEq transitivity. Canonical environment/body correspondence for
arbitrary source action paths remains open; no compatibility axiom is added.

## Fresh presentations keep the literal tests

[SourceNamedFreshStatic](../../ExplainableCrypto/Helios/Symbolic/SourceNamedFreshStatic.lean)
proves `RepresentsFrame.common_fresh`. One pair of base/channel permutations
moves both complete frames under common fresh name policies. Old handle indices
and all values remain. Protected names outside the original prefix stay fixed.
`StaticEq.fresh_witness` attaches the full equality certificate to a common
presentation avoiding any finite external set.

`StaticEq.test_witness` accepts arbitrary literal recipes `r` and `s`, freshens
both presentations away from their full name support, and proves equality-test
agreement for exactly those original recipes. It also retains the certificate
for all public tests in the new policy. This does not assert that the old fixed
policy already permits a literal equal to an old bound name. The later
[compatibility proof](helios-source-frame-compatibility.md) now transfers universal
frame equations for every unchanged literal test through independent witnesses.

## Reached elections and silent paths

[SourceNamedElectionStatic](../../ExplainableCrypto/Helios/Symbolic/SourceNamedElectionStatic.lean)
transports presentations and static witnesses through finite internal paths.
`reachable_source_staticEq` applies the full reached-view theorem for fresh
historical names, valid candidate substitutions and any reached stage. It
compares the actual swapped-vote `restrictedState` terms, with their concrete
source bodies and complete frames. `reachable_structural_source_staticEq`
allows arbitrary structural representatives on both sides. No channel-freshness
premise is needed solely to compare these current frames; operational matching
has its own channel premises.

## Controls and remaining work

[SourceNamedStaticSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceNamedStaticSPOT.lean)
contains twelve public kernel controls. Actual restricted frames supply a
reflexive witness; missing domains and duplicate definitions cannot supply one.
The required frame-observation certificate rejects zero versus one for every
common name policy. This is a certificate-level separation result, not an
unproved reflection theorem about every arbitrary Named presentation.

A paired positive/negative control has identical current frames but different
possible next outputs, explicitly showing why the static clause does not prove
dynamic matching. Output reclosure recovers the old complete presentation.
Reached zero-extra, two-extra and rejected elections obtain Named static
witnesses. A full fourth-field recipe keeps an old private literal unchanged
while its common frame presentations freshen. A real private communication
retains the same witness through a nonempty internal path.

The independent reality oracle is Section 5.1.2 Definition 1's common restricted
substitutions and Definition 2's static clause. These are structural/witness
kernel proofs with independent controls, not a new randomized cryptographic
campaign or an inference from failed search. No existing source rule or E
equation changes. Witness existence and full recipe quantification are explicit.

The subsequent [Named permutation transport](helios-source-named-permutations.md)
now moves and reflects complete structural/action paths, presented frames and
static witnesses under independent name bijections. Canonical environment/body
correspondence across arbitrary Named action paths, remaining source
admissibility/action matching and weak labelled bisimilarity/
symbolic secrecy remain open. See the [blueprint](helios-proof-blueprint.md),
[variable admissibility](helios-source-named-admissibility.md),
[full frame projection](helios-source-frame-projection.md), and
[task list](../../task%20list.md).

Integrated verification for the Named static-witness checkpoint: `lake build` passes **3915 jobs**, with
**3391** nonempty standard-only and **57** axiom-free reports. The claim audit
covers **2462** public theorem entries and **100** current-status documents.
All seven changed Lean sources have current oleans; **1246** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-named-static-full-build.log`.
This increment adds 38 theorem audits, including twelve public kernel controls.
Targeted controls pass 1297 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-named-static-verification.txt`.

[Common-policy alignment](helios-source-policy-padding.md) now gives any two
independent StaticEq witnesses a single policy, all four actual source
presentations and both full frame certificates. Freshening and unused-policy
padding discharge the alignment side conditions. The subsequent
[independent compatibility proof](helios-source-frame-compatibility.md) now
compares the two middle presentations and proves general Named.StaticEq
transitivity. Universal frame equations supply the missing comparison.

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
