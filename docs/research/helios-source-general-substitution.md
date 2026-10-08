# General active substitution in the source semantics

B9 now includes the active-active instance of Figure 3 Subst and derives
substitution through every current Extended context. General Named contexts
use a fresh name-prefix representation that avoids capture of the full
replacement term. The provider remains present throughout. This closes the
documented plain-only substitution limitation for the current finite syntax;
it intentionally expands the source structural relation. Full E is unchanged.
Fresh/injective assignment selection for arbitrary action paths and the final
secrecy theorem remain open. [Independent presentation compatibility](helios-source-frame-compatibility.md)
and Named static transitivity are now proved. B9/B10 stay at 8/10 milestones (80%,
unweighted).

## Source rule and general derivation

[SourceExtendedSyntax](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedSyntax.lean)
adds `Structural.substActive`: beside `{m/x}`, another distinct active definition
`{n/y}` can become `{n{m/x}/y}`. Both active domains and the provider `{m/x}`
remain. Distinct domains are the active-definition side condition; the existing
SubstPlain rule continues to handle plain processes.

[SourceExtendedSubstitution](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedSubstitution.lean)
defines `substFree` over all current Extended constructors. It substitutes in
full payloads and plain continuations, keeps active domains fixed, and shifts
both the variable and replacement through each variable restriction.
`Structural.substExtended` derives the complete source rule for contexts that
do not redefine the provider variable. Parallel structure distributes the
retained provider without duplicating it; New-Par carries it under variable
restriction with the correct Some shift. `substExtended_of_unique` discharges
the no-redefinition premise from the source's unique-definition invariant.

The substitution function preserves exported domains and uniqueness and
commutes with injective variable renaming, name mapping and frame extraction.
No proof replaces a bound variable by an unshifted outer payload.

## Capture avoidance for Named contexts

[SourceNamedGeneralSubstitution](../../ExplainableCrypto/Helios/Symbolic/SourceNamedGeneralSubstitution.lean)
first proves the embedded Extended case. `Structural.substNamed_fresh` then
handles any current Named context by finding an actual structural representative
under a name prefix fresh for the provider's entire payload. It substitutes in
the Extended body beneath that prefix and moves the retained provider back
outside. The result includes the chosen context representative, its domain
side condition, name freshness and the actual source structural path.

This is capture-avoiding substitution expressed through a fresh representative;
it does not claim that naive recursive substitution beneath unchanged name
binders is sound. Source uniqueness supplies the domain condition through
`substNamed_fresh_of_unique`. The earlier syntax exclusions for replication,
mobile channels and arbitrary under-prefix name creation remain separate.

## Existing invariants rechecked against the stronger relation

The structural inductions in SourceExtendedExports, SourceUniqueDefinitions,
SourceChannelSupport, SourceFrameStructure, SourceNameExtended,
SourceStructuralVariableRename and SourceInterpretationStructure now include
SubstActive. All exported domains, unique definitions, channel support, full
frame extraction, name mapping and injective variable renaming still transport.
A term replacement naturality lemma supports variable renaming.

`subst_active_term_equivE` uses the retained provider equation in the realizing
environment. `realizes_substActive` then preserves both active constraints and
the complete interpreted body. Existing internal/free/bound interpretations,
Named actions, frame witnesses and controls are rebuilt against this expanded
relation; the new rule is not bypassed by a separate operational model.

## Controls and remaining work

[SourceExtendedSubstitutionSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedSubstitutionSPOT.lean)
contains fourteen public kernel controls. A dependent alias frame takes a real
normalization step and remains well-formed. Its normalized form gives a
complete two-handle ground presentation and Named static witness. Arbitrary
structural paths cannot change its value to one, and a dependent active value
cannot be replaced by zero when the provider constraint is omitted.
Duplicate provider definitions remain invalid.

Literal controls distinguish a restricted binder, a later input binder and an
outer variable through substitution; an unshifted replacement is rejected.
General nested-context and full fourth-field proof substitutions are derived.
A Named context whose private binder collides with the provider's external
literal is freshened before substitution. Full E distinguishes the fresh name
from the external literal, ruling out the equality introduced by naive capture.

The reality oracle is Figure 3's Subst rule on general extended A, retaining its
provider substitution. The old plain-only limitation was documented; no proof
search failure is used as evidence of old nonderivability. These are source
structural proofs and independent controls, not a new randomized cryptographic
campaign or security inference. This increment changes source-rule coverage and
updates its model record; it does not alter any cryptographic equation.

The next increment derives [local-definition elimination](helios-source-local-normalization.md)
through Extended and fresh Named contexts. General constraint-system
normalization and canonical environment/body correspondence remain open where
required for arbitrary source action paths. Remaining admissibility/action matching
and source weak labelled bisimilarity/symbolic secrecy stay open. See the
[blueprint](helios-proof-blueprint.md),
[active source semantics](helios-source-active.md),
[interpretation](helios-source-interpretation.md), and
[task list](../../task%20list.md).

Integrated verification at this substitution checkpoint: `lake build` passes **3923 jobs**, with
**3457** nonempty standard-only and **57** axiom-free reports. The claim audit
covers **2528** public theorem entries and **102** current-status documents.
All fourteen changed Lean sources have current oleans; **1269** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-general-substitution-full-build.log`.
This increment adds 27 theorem audits, including fourteen public kernel controls,
and explicitly checks the new source-rule constructor and substitution function.
Targeted controls pass 1143 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-general-substitution-verification.txt`.

[Full Named body interpretation](helios-source-named-body.md) now proves
all-rule structural invariance and canonical/prenex full frame/body interpretation
under one assignment of both name sorts. That assignment may collide;
fresh/injective witness selection through arbitrary action paths and operational
correspondence remain open.
