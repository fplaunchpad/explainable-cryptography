# Explicit source name restrictions

B9 now has explicit sorted name binders in extended evaluation contexts, source
name structural/Scope rules, and forward derivations of every evaluated scoped
transition through those binders. Inputs carry their literal public recipes;
outputs retain all restricted names around the complete captured active frame.
The name/channel policy checks are exactly the repeated label-freshness checks
used by the forward bridge. These are machine-checked supporting results.
B9/B10 remain incomplete at 8/10 unweighted milestones (80%).

## Syntax and source rules

[SourceNameSupport.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameSupport.lean)
computes finite syntactic name support for terms, formulas, plain agents,
extended processes and free labels. All proof fields count. `SourceName.base`
and `SourceName.channel` are different sorts even at the same numeric index.
`Term.public_iff_nameSupport` characterizes public recipes by absence of
restricted literals. Input labels contain their channel and all literal recipe
names; output-variable labels contain their channel alone.

[SourceNameRestrictionSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameRestrictionSyntax.lean)
defines `Named`: embedded existing extended syntax, parallel composition,
explicit name restriction and variable restriction. Name restriction removes
its binder from `freeNames`; `allNames` also records nested binders for alpha
freshness. Consistent name mapping and typed variable renaming are separate.
The name map has a permutation inverse and commutes with variable renaming.

The structural relation includes the existing variable/active structural rules,
evaluation contexts, parallel laws, New-0, name/name and name/variable New-C,
typed variable/variable exchange, and New-Par. Name New-Par requires absence
from the other component's free names. Variable New-Par shifts that component
past the new variable. Same-sort alpha rules swap a bound base/channel name
and all its occurrences, requiring the new name to be absent from the body's
entire name support, including nested binders. This is a conservative
capture-free presentation of the source alpha rule; completeness of alpha
normalization and its connection to every observation/transition remain open.

[SourceNameRestrictionRules.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameRestrictionRules.lean)
adds internal reduction under name/variable restrictions and the source
structural/context closures. Free-label Name Scope checks absence of the binder
from the actual complete label. Bound-variable output can cross a name binder
exactly when that binder is not its channel. The name binder remains in the
target around the newly exported active value. Open-Atom, variable Scope, Par
and Struct retain their typed variable binding behavior. Closure theorems lift
internal/free/bound-output derivations through any finite binder list, subject
to the appropriate label freshness premises.

## Canonical restricted states and forward correspondence

[SourceNameRestrictionBridge.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameRestrictionBridge.lean)
constructs a concrete name-binder list from the restricted base-name and hidden
channel policies. Its membership characterizations distinguish the two sorts;
`restrictionNames_nodup` proves pairwise distinct binders. List extraction from
finite sets is noncomputable but introduces no logical assumption beyond the
standard Lean dependencies.

`input_restriction_fresh_iff` proves that every binder is absent from the input
label exactly when its channel is public and its recipe is public.
`output_restriction_fresh_iff` reduces bound-variable-output freshness to its
public channel; it imposes no public-syntax requirement on the emitted payload.

`restrictedState` puts those actual binders around the full active frame/process.
`restricted_tau_derivable` and `restricted_input_derivable` derive every wrapper
step through source evaluation contexts/Scope. `restricted_output_derivable`
produces the full raw bound-output target under all name restrictions, then
proves structural correspondence to the wrapper target after the explicit
fresh-variable/last-handle bijection. The result reuses the checked atomic/active
derivations; it adds no primitive full-message output or redacted frame rule.

## Controls and remaining obligations

[SourceNameRestrictionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameRestrictionSPOT.lean)
has fourteen kernel controls. Independently written syntax checks that a base
binder leaves the same-index channel free, valid extrusion and base/channel
alpha conversion, capture-failing freshness premises and nested-binder freshness.
The complete fourth proof field blocks input Scope when it contains a restricted
literal; a public handle is allowed. Private visible labels fail Scope freshness,
while private internal communication remains derivable. Compound secret-bearing
output retains its name restriction and full active payload. New-0, actual voter
input and complete raw output/canonical capture exercise the new rules.

Negative freshness controls concern the stated rule premises. They do not prove
the absence of every derivation through arbitrary structural equivalence. The subsequent
[channel-closure proof](helios-source-channel-closure.md) now excludes private
channel actions through that entire closure and after arbitrary internal
execution. The full payload/target converse remains open; a checked alpha-input
counterexample excludes inferring the original fixed recipe policy. Coherent
[fresh representatives](helios-source-fresh-names.md) are now proved for both
actual states, with public recipes and preserved full frame observations. Named-frame observation
extraction and admissibility preservation also remain to be connected. Syntactic
base-name support is not assumed invariant under unrestricted raw EqE Rewrite.

This syntax adds restrictions in evaluation contexts. It does not yet represent
name creation beneath arbitrary plain input/output/conditional prefixes,
replication or mobile channel values. The historical protocol's outer voter
nonce/let construction must still be linked to the allocated finite body.
The actual source theorem and final weak labelled bisimilarity remain open.
This increment uses structural proofs and kernel controls, with no new randomized
security campaign or inference from search failure.

See the [blueprint](helios-proof-blueprint.md),
[renamed observations](helios-source-renamed-observations.md),
[active-frame input](helios-source-frame-input.md) and
[atomic output](helios-source-atomic-output.md).

Integrated verification for the explicit name-restriction checkpoint: `lake build` passes **3846 jobs**, with
**2942** nonempty standard-only and **47** axiom-free reports. The claim audit
covers **2003** public theorem entries and **90** current-status documents.
All seven changed Lean sources have current oleans; **1110** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-name-restriction-full-build.log`.
This increment adds 34 theorem audits, including fourteen kernel controls, and
20 definition checks. Targeted controls pass 1217 jobs. Freshness/hole/link
evidence: `tmp/variable-overlap/source-name-restriction-verification.txt`.
