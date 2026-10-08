# Eliminating local active definitions

Current follow-up: [scoped program captures](helios-source-scoped-capture.md)
now handles interleaved ScopedTermProgram base-name/local scopes under Hoistable
and old-frame name freshness, with actual full combined-policy presentations.
General reachable reconstruction and final secrecy remain open.

Current follow-up: [dependent program captures](helios-source-program-capture.md)
now reconstructs actual Scope targets for every finite existing TermProgram,
including dependent local definitions and full Named frame presentations.
General extraction through reachable structural representatives remains open.

Current follow-up: [recipe capture reconstruction](helios-source-recipe-capture.md)
now gives full provider-context substitution and actual ground presentations
for explicit fresh recipe-valued captures. Extracting that form from arbitrary
reachable representatives, and final secrecy, remain open.

Current update: [binder rigidity](helios-source-binder-rigidity.md) now proves
full Named.Structural separation of the cyclic joint pair and excludes all its
ground frame presentations/StaticEq partners. Structural opening comparison is
stronger, and Extended bound-output rigidity is checked. Earlier statements
leaving these facts open below are historical; reconstruction sufficiency remains open.

Current update: [local rigidity](helios-source-local-rigidity.md) refutes the
Extended normalization implication from WellFormed/nonempty full class alone.
The counterexample also has an embedded joint opening; Named.Structural
separation and a sufficient reconstruction invariant remain open.

B9 now derives local-definition elimination through every current Extended
context and through fresh representatives of arbitrary current Named contexts.
The full provider payload is substituted before its local variable is removed.
This uses the existing Subst, New-Par, Alias and parallel rules; it adds no
source rule or cryptographic equation. B9/B10 remain incomplete at 8/10
unweighted milestones (80%).

## Exact instantiation

[SourceExtendedInstantiation](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedInstantiation.lean)
defines `Extended.Instantiates σ a b`. Plain processes and all active payloads
receive the complete substitution. An active domain `x` can become domain `y`
only when `σ x = var y`. Parallel composition recurses on both sides; variable
restrictions lift the substitution past the fresh binder. The relation handles
an empty target variable type without inventing a default variable.

`instantiates_exists` constructs a result when every exported source domain
maps to a variable. `Instantiates.unique` fixes that result exactly.
`instantiates_rename` and `Instantiates.comp` connect the relation to existing
renaming and substitution composition. `instantiates_substFree` connects it to
the retained-provider substitution under the no-redefinition premise.
`Instantiates.replace_fresh` proves that substituting a fresh local and then
keeping its unused binder gives exactly the renamed instantiated context.
These are syntax equalities and relations, not choices of equivalent ground
values for arbitrary cyclic constraints.

## Derived normalization

[SourceLocalNormalization](../../ExplainableCrypto/Helios/Symbolic/SourceLocalNormalization.lean)
proves `Structural.let_normalize`. Its source is
`newVar (par (active none (shiftTerm m)) a)`; its target is the exact result `b`
of `Instantiates (inputSubst m) a b`. The context must not export `none`.
The type of `m : Term V` ensures that the provider does not refer to its own
fresh local, while permitting arbitrary old variables and full terms.

`let_normalize_exists` constructs both the instantiation and actual structural
path for every context satisfying the side condition. `let_normalize_of_unique`
derives that condition from unique definitions of the original local process.
The proof applies general Subst, moves the context outside the now-unused
variable restriction, and discharges the retained provider with Alias and Par-0.
It extends the existing plain-process `let_eliminate` derivation to active
contexts and nested variable restrictions.

`Instantiates.realizes` preserves the entire interpretation in both directions,
with the environment composed through the substitution. `local_realizes`
specializes this to the environment extended by the evaluated provider value.
The complete active constraints and the specified interpreted body remain in
the statement. `local_exports` preserves every surviving old active domain.

## Private names

[SourceNamedLocalNormalization](../../ExplainableCrypto/Helios/Symbolic/SourceNamedLocalNormalization.lean)
proves `Named.let_normalize_fresh`. An arbitrary Named context gets an actual
structural representative with a name prefix fresh for the unchanged provider.
The local variable moves under that prefix, the Extended normalization runs,
and the result retains that same fresh name prefix. The conclusion includes
the chosen context representation, prefix freshness, no-redefinition condition,
exact instantiation and actual Named structural derivation. Unique definitions
supply the side condition in `let_normalize_fresh_of_unique`.

## Controls and limits

[SourceLocalNormalizationSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceLocalNormalizationSPOT.lean)
contains fifteen public kernel controls. Two dependent restricted definitions
normalize into one public active handle, retain its exact domain and give a
complete ground-frame presentation. An arbitrary structural path to a wrong
public value is rejected. Another fixture substitutes through an input while
preserving that input's binder and works with an empty outer variable type.
A captured input result is rejected by uniqueness of exact instantiation.
The full fourth proof field is substituted. Duplicate local definitions cannot
be erased even when their payloads agree, and an active domain cannot be
replaced by a name.

A concrete Named derivation changes the context's private literal 40 to 41
while retaining the provider's external literal 40. A full-E control separates
those literals. A separate control instantiates the general fresh-prefix
existence theorem. Expected binder/domain results are calculated from the
literal fixtures. This is structural algebra and kernel control evidence;
there is no new randomized cryptographic campaign or search-based security
inference. The reality oracle is the existing Figure 3 structural rules.

This closes elimination of a local provider whose value is independent of its
own binder. General constraint-system normalization where needed, canonical
environment/body correspondence through arbitrary Named action paths, remaining
admissibility/action matching and final weak labelled bisimilarity/symbolic
secrecy remain open. In particular,
a ground interpretation alone is not claimed to imply structural normalization.
See the [blueprint](helios-proof-blueprint.md) and
[task list](../../task%20list.md).

Integrated verification at this local-elimination checkpoint: `lake build` passes **3927 jobs**. The build reports
**3482** nonempty standard-only and **61** axiom-free results; the claim audit
covers **2557** public theorem entries and **103** current-status documents.
All six changed Lean sources have current oleans, and **1279** local links
resolve. No proof holes, custom axioms, warnings or errors were found in the
checked scope; `git diff --check` passes. This increment adds **29** theorem
audits, including **15** public kernel controls. The substitution graph itself
is explicitly checked. Targeted controls pass **1146 jobs**.
Build log: `tmp/variable-overlap/source-local-normalization-full-build.log`.
Freshness/hole/link evidence:
`tmp/variable-overlap/source-local-normalization-verification.txt`.

The next [policy-compatibility increment](helios-source-policy-padding.md)
handles unused restrictions and common policies for independent static witnesses.
The subsequent [independent compatibility proof](helios-source-frame-compatibility.md)
now discharges middle-frame observations and Named static transitivity.
Fresh/injective assignment selection through arbitrary action paths remains open.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.
