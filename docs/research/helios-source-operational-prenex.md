# Common-prefix factorization of Named actions

B9 now factors every current Named internal reduction and free visible action
through one common name prefix and an actual Extended action. Structural paths
connect both raw endpoints to those factored endpoints. Free actions retain
exactly their original labels, and the common prefix binds none of the label's
names. The converse reconstructs the original Named action. This is an exact
operational factorization for these two action kinds, not full symbolic secrecy.
B9/B10 remain open at 8/10 milestones (80%, unweighted).

## Both endpoints move together

[SourcePairedPrenex](../../ExplainableCrypto/Helios/Symbolic/SourcePairedPrenex.lean)
combines two endpoint bodies under a common prefix with one parallel context.
The acting prefix is freshened simultaneously for both bodies against the
context's names and a protected set. Protected names were outside the original
prefix and therefore remain fixed by the common base/channel permutations.
The context itself gets one fresh prenex body, shared by both endpoints, whose
prefix avoids both acting bodies. Both endpoint structural paths use the same
concatenated prefix and the same context body. No freshness or context equality
is left as an unproved callback.

[SourceNamedInternalPrenex](../../ExplainableCrypto/Helios/Symbolic/SourceNamedInternalPrenex.lean)
proves `Reduction.prenex` by induction over every current Named reduction rule.
The result contains one actual Extended.Reduction. Name contexts extend the
common prefix; variable contexts commute with it and become Extended newVar.
Parallel contexts use the paired construction. Arbitrary Struct paths compose
with the endpoint witnesses. `reduction_iff_prenex` reconstructs the Named step
with the same prefix and source structural paths. No zero-step substitute is used.

## Exact free labels

[SourceFixedLabelNames](../../ExplainableCrypto/Helios/Symbolic/SourceFixedLabelNames.lean)
proves that variable renaming retains literal term-name support and that fixing
all supported base names fixes the complete term. Input shift therefore retains
complete label support. A map fixing a free label's sorted name support fixes
that entire label, including all names deep inside an input recipe and its
static channel. Variable output handles keep their indices.

[SourceNamedFreePrenex](../../ExplainableCrypto/Helios/Symbolic/SourceNamedFreePrenex.lean)
proves `FreeStep.prenex` for every current constructor: embedding, name Scope,
input/output variable Scope, both Par contexts and arbitrary Struct. It produces
one actual Extended.FreeStep with the original label, and every prefix binder
is fresh for that label. The paired parallel construction protects the whole
label support before renaming its acting bodies. `freeStep_iff_prenex` rebuilds
the Named action using the checked name-Scope freshness conditions.

This result handles the earlier alpha-input boundary without reinstating its
false fixed-original-policy claim. The derived prefix can use different private
names; the original received recipe stays unchanged. Publicness is relative
to the factored prefix's binders, not inferred from the source's original list.

## Freshness and interpretation interface

[SourceFreshOperationalPrenex](../../ExplainableCrypto/Helios/Symbolic/SourceFreshOperationalPrenex.lean)
gives distinct common prefixes avoiding any finite external name set. Internal
steps use one shared name permutation. Free steps additionally avoid the entire
original label support and fix that label during freshening. These statements
allow avoidance of the other world's support while retaining the actual action.

The interpreted corollaries apply the checked Extended interpretation to the
factored source: every supplied realization of that body gives an actual Tau
or exact-input/full-output interpreted visible step and a realized factored
target. They do not assume that a realization of some other canonical Named
representative automatically transfers to this particular Extended body.
Establishing that representative correspondence remains open.

## Controls and remaining work

[SourceOperationalPrenexSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceOperationalPrenexSPOT.lean)
contains twelve public kernel controls. A private handshake beside the actual
frame factors to one Extended reduction, can use a distinct externally fresh
prefix, and reconstructs its Named action. The retained alpha-input fixture
factors with literal 40 unchanged; its prefix cannot bind that received literal.
It can avoid a second world's names and reconstruct the exact Named input.
A name appearing only in a proof's fourth field is in label support; changing
it does not fix the label, while an unrelated permutation does. Private input
remains blocked, and an independently supplied actual-frame realization retains
a genuine internal step.

No Named/Extended structural or operational rule, E equation or public
observation was changed. These are general structural kernel proofs with
independent controls, not a new randomized cryptographic campaign or a security
claim based on failed attack search.

The subsequent [bound-output factorization](helios-source-bound-prenex.md) now
covers every bound-output constructor, including shifted old contexts and the
exchanged Scope binder. Next relate factored source/target realizations to
canonical complete frames through Named structural/alpha paths. Connect named
observations/admissibility and outer voter nonce/let syntax, then assemble source
weak labelled bisimilarity and symbolic secrecy. Name-prefix existence and
operational factorization do not by themselves solve arbitrary active constraints
or prove the full source correspondence. General replication, mobile channels
and name creation under arbitrary plain prefixes remain outside the current
finite historical syntax.

See the [blueprint](helios-proof-blueprint.md),
[Named prenex representatives](helios-source-name-interpretation.md),
[Extended visible interpretation](helios-source-visible-interpretation.md),
[fresh name policies](helios-source-fresh-names.md) and
[task list](../../task%20list.md).

Integrated verification for the internal/free factorization checkpoint: `lake build` passes **3889 jobs**, with
**3220** nonempty standard-only and **48** axiom-free reports. The claim audit
covers **2282** public theorem entries and **96** current-status documents.
All eight changed Lean sources have current oleans; **1195** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-operational-prenex-full-build.log`.
This increment adds 26 theorem audits, including twelve public kernel controls.
Targeted controls pass 1271 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-operational-prenex-verification.txt`.

[Full Named visible interpretation](helios-source-named-visible.md) now supplies
the previously separate canonical-to-prenex visible connection for every actual
free/bound action, retaining full target interpretation. Finite-support
faithfulness is sufficient for Extended internal transport, but fixed old
environment injectivity is refuted by an alpha/dead-field control. General Named
internal correspondence, required new-frame presentation/relation invariants
and final source bisimilarity/secrecy remain open.
