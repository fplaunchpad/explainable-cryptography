# Name permutations of complete Named derivations

B9 now transports and reflects every current Named structural and operational
rule under independent bijections of base names and channels. This includes
alpha conversions inside arbitrary contexts, complete labels, variable Scope
and bound-output contexts. Frame presentations and Named static witnesses move
with their complete values and name policies. These are machine-checked
transport results needed when comparing differently named presentations;
fresh/injective assignment selection through arbitrary action paths remains open.
[Independent frame compatibility](helios-source-frame-compatibility.md) now
proves public test agreement for unrelated presentations and Named static
transitivity. B9/B10 stay at 8/10 milestones (80%, unweighted).

## Full support and alpha conversion

[SourceNamedNameSupport](../../ExplainableCrypto/Helios/Symbolic/SourceNamedNameSupport.lean)
proves support-image formulas for formulas, agents, Extended processes, free
labels and Named all-name support. Free-name support has the image formula
under name permutations; injectivity prevents a free name from collapsing onto
a binder. Membership reflection gives the corresponding freshness conditions.
All term fields and nested binders count.

The base/channel swap-conjugation lemmas state that globally renaming a local
alpha swap gives the swap of the renamed endpoints. Both name sorts stay
separate and every variable binder remains in place.

[SourceNamedNameStructure](../../ExplainableCrypto/Helios/Symbolic/SourceNamedNameStructure.lean)
proves `Named.Structural.mapNames` for every constructor, including fresh name
extrusion, variable extrusion/exchange and both alpha rules. Alpha's target
freshness follows from all-name membership reflection; its renamed body follows
from swap conjugation. `Structural.mapNames_iff` reflects an arbitrary mapped
path by the inverse permutations.

## Actions and complete targets

[SourceNamedNameActions](../../ExplainableCrypto/Helios/Symbolic/SourceNamedNameActions.lean)
proves forward and reverse transport for internal reductions, free actions,
bound outputs and finite internal paths. Labels move with the source and target.
Name Scope retains full-label freshness; variable Scope keeps the shifted
message or old variable. Bound-output Scope keeps its binder exchange and both
parallel cases keep the shifted old context. Arbitrary structural paths at the
endpoints use the newly checked structural transport.

These results apply a global permutation, so literal query names move too.
The earlier fresh-presentation result keeps a query fixed while choosing fresh
representatives around it. Neither result treats the old fixed policy as the
renamed policy or deletes a payload field.

## Presented frames and static witnesses

[SourceNamedPresentationNames](../../ExplainableCrypto/Helios/Symbolic/SourceNamedPresentationNames.lean)
proves `canonicalFrame_mapNames`. The mapped canonical prefix may have a
different list order from the newly canonicalized name sets; source New-C
reorders it. Every active value follows the same base-name permutation.

`RepresentsFrame.mapNames` transports an entire presentation path, and
`representsFrame_mapNames_iff` reflects it with the inverse permutations.
`Named.StaticEq.mapNames` and `staticEq_mapNames_iff` transport and reflect both
complete presentations and the full all-public-recipe certificate. No
compatibility assumption about unrelated canonical presentations is added.
The separate [compatibility proof](helios-source-frame-compatibility.md) now
discharges that comparison using universal frame equations.

## Controls and evidence

[SourceNamedPermutationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceNamedPermutationSPOT.lean)
contains thirteen public kernel controls. They transport an actual alpha path,
conjugate a swap affecting a fourth-field recipe, and show why collapsing maps
can destroy both free-name support and alpha freshness. The retained alpha-input
action moves its exact channel and literal; keeping the old literal is rejected.
Nested bound output transports and reflects. A complete presentation moves its
private key value and policy together; keeping the old policy is rejected.
Named static witnesses transport and reflect. A renamed private channel remains
blocked, and an actual private communication transports.

The reality oracle is capture-free uniform renaming of Figure 3 and the complete
restricted-substitution presentations of Definition 1. These are structural
kernel proofs with independent controls; no new randomized cryptographic
campaign or inference of security from failed search is claimed. No existing
source rule, equation, frame value or public observation is weakened.

The subsequent [general substitution increment](helios-source-general-substitution.md)
adds active-active Subst and derives substitution through the current Extended/
fresh Named contexts; these permutation results are rechecked for that rule.
Next: normalize dependent constraints, compare unrelated canonical presentations
and transfer canonical interpretations through arbitrary Named alpha paths. Remaining source
admissibility, outer voter nonce/let syntax and source weak labelled bisimilarity/
symbolic secrecy remain open. See the [blueprint](helios-proof-blueprint.md),
[Named static witnesses](helios-source-named-static.md),
[earlier Extended/global name transport](helios-source-name-permutations.md), and
[task list](../../task%20list.md).

Integrated verification for the Named permutation checkpoint: `lake build` passes **3920 jobs**, with
**3430** nonempty standard-only and **57** axiom-free reports. The claim audit
covers **2501** public theorem entries and **101** current-status documents.
All seven changed Lean sources have current oleans; **1257** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-named-permutation-full-build.log`.
This increment adds 39 theorem audits, including thirteen public kernel controls.
Targeted controls pass 1302 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-named-permutation-verification.txt`.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.
