# Unused restrictions and common frame policies

B9 now aligns any two independent Named static-equivalence witnesses under one
common base-name policy, retaining all four actual source presentations and
both full frame-equivalence certificates. This closes policy alignment between
independently chosen witnesses. The later
[compatibility proof](helios-source-frame-compatibility.md) now discharges the
middle-frame equality comparison and proves general Named static transitivity.
Final symbolic secrecy remains open. B9/B10 stay at 8/10 unweighted milestones.

## Unused source restrictions

[SourceUnusedRestrictions](../../ExplainableCrypto/Helios/Symbolic/SourceUnusedRestrictions.lean)
derives `Structural.name_unused` from New-Par, New-0 and Par-0 whenever the
restricted name is absent from the complete body's free names. It applies to
arbitrary current Named bodies, including executable processes. The finite-prefix
variant removes an entirely unused prefix. A duplicate restriction is removable
because its name is already bound by the inner restriction. The exact free-name
formula for a prefix accounts for every binder and both name sorts.

## Full equality observations survive padding

[SourceFramePolicies](../../ExplainableCrypto/Helios/Symbolic/SourceFramePolicies.lean)
defines `Frame.withPolicy`, which retains every complete frame value, and
`Frame.nameSupport`, the finite union of literal names in all handle values.
Changing the policy index alone supplies no semantic or source proof.

`staticEq_insert_unused_iff` proves that forbidding a name absent from both
complete frames preserves and reflects full all-public-recipe static equivalence.
For reflection, an arbitrary test mentioning the newly forbidden literal uses
an alternate fresh literal. Swapping those literals fixes both frames; full E
reflects through the bijection. Thus the proof recovers the original equality
observation, even when the original test is inadmissible under the padded policy.

`staticEq_union_unused_iff` extends this to any finite policy addition. Names
already forbidden by the old policy need no additional freshness premise.
Every newly forbidden name must be absent from both complete frame supports.
`StaticEq.withPolicy` separately records the unconditional forward implication
when increasing a restriction set. The iff theorem supplies the additional,
load-bearing reflection result.

## Canonical source paths

[SourceCanonicalPolicyPadding](../../ExplainableCrypto/Helios/Symbolic/SourceCanonicalPolicyPadding.lean)
connects full frame support to the exact support of active-frame syntax.
Canonical prefix reordering exposes each added base binder; unused-binder
elimination gives an actual source structural path back to the original frame.
`RepresentsFrame.pad_policy` retains that path when padding a presentation.

Extracted active frames contain no channels, so their hidden channel policy can
also change through an actual structural path. This is a statement about pure
frames. An executable body may use those channels and cannot discard their
restrictions on this basis.

## Independently chosen witnesses

[SourceCommonFramePolicy](../../ExplainableCrypto/Helios/Symbolic/SourceCommonFramePolicy.lean)
first aligns two presentations with explicit cross-freshness conditions.
`Named.StaticEq.common_policy` then discharges those conditions for any two
Named static-equivalence witnesses:

1. Freshen the first pair against the second pair's full values and old policy.
2. Freshen the second pair against the first pair's new full values and policy.
3. Use the protected-name condition to show the second permutation cannot
   introduce any first-policy name into either second-pair frame.
4. Pad both pairs to the union of their fresh policies and retain both full
   static-equivalence certificates and all four source presentation witnesses.

No extra freshness premise is left to the caller. The theorem does not compare
the two middle frames. The later [compatibility proof](helios-source-frame-compatibility.md)
compares two presentations of the same process using universal frame equations.

## Controls and remaining work

[SourcePolicyPaddingSPOT](../../ExplainableCrypto/Helios/Symbolic/SourcePolicyPaddingSPOT.lean)
contains fifteen public kernel controls. Distinct full syntax with equal E-values
keeps its observations under unused finite padding. A fresh literal replaces a
forbidden literal in a test. A name used only in a proof's fourth field fails
the freshness premise. Used literals change recipe admissibility; used channel
restrictions cannot be removed from executable processes. Canonical padding
and presentation retention have actual source paths. Two independent pairs
with mutually colliding private/free literals obtain common-policy witnesses.
Zero and one remain distinguishable under any padded policy, and two unrelated
pairwise certificates do not imply cross-pair equivalence.

These are general structural/permutation proofs and independently calculated
literal controls. No new randomized cryptographic campaign or search-based
security conclusion is claimed. The source structural relation and full E
remain unchanged. The reality oracle is the existing Figure 3 name rules and
the all-public-recipe definition.

Canonical environment/body
correspondence through arbitrary Named structural paths, normalization of the
relevant active constraints where needed, remaining admissibility/action matching
and source weak labelled bisimilarity/symbolic secrecy remain open. See the
[blueprint](helios-proof-blueprint.md) and [task list](../../task%20list.md).

Integrated verification at this policy-alignment checkpoint: `lake build` passes **3932 jobs**. The log reports
**3520** nonempty standard-only and **61** axiom-free results. The claim audit
covers **2595** public theorem entries and **104** current-status documents.
All seven changed Lean sources have current oleans; **1288** local links resolve.
No proof holes, custom axioms, warnings or errors were found in the checked
scope; `git diff --check` passes. This increment adds **38** theorem audits,
including **15** public kernel controls, and explicitly checks the two new
frame definitions. Targeted controls pass **1145 jobs**.
Build log: `tmp/variable-overlap/source-policy-padding-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-policy-padding-verification.txt`.

The next [voter-computation increment](helios-source-voter-computation.md)
adds the explicit local computation blocks. The later
[independent compatibility proof](helios-source-frame-compatibility.md) uses this
common-policy construction to derive Named.StaticEq transitivity.
