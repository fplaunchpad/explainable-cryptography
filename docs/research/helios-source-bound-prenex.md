# Bound-output factorization and structural variable renaming

B9 now factors every current Named bound output through one actual
Extended.BoundOutput under a common name prefix, with structural paths from
both raw endpoints and converse reconstruction. The exact output channel stays
public relative to that prefix, and the target uses precisely the additional
Option variable required by the source rule. Together with the prior internal
and free-action results, all three current Named action kinds have checked
operational prenex factorizations. Canonical-frame/interpretation correspondence
and the full secrecy proof remain open. B9/B10 stay at 8/10 completed milestones
(80%, unweighted, not an effort estimate).

## Injective variable renaming

[SourceVariableRenameTools](../../ExplainableCrypto/Helios/Symbolic/SourceVariableRenameTools.lean)
proves injectivity of lifted Option maps, lifted input substitution, shifted-term
renaming and complete replacement/substitution naturality. Injectivity prevents
an unrelated old variable from acquiring the substituted variable's image.
The Formula/Agent/Extended name-support results retain all literal base/channel
names under variable renaming, including nested inputs and every payload field.

[SourceStructuralVariableRename](../../ExplainableCrypto/Helios/Symbolic/SourceStructuralVariableRename.lean)
proves transport of every Extended.Structural rule under an injective variable
map. Alias, SubstPlain, Rewrite, fresh New-Par and all symmetric/transitive and
context paths are included. Names and channels do not change in these maps.

[SourceNamedVariableRename](../../ExplainableCrypto/Helios/Symbolic/SourceNamedVariableRename.lean)
proves Named renaming composition, unchanged free/all-name support and commutation
with the two-binder swap. It transports every Named.Structural constructor under
an injective variable map, including alpha, name extrusion and Name-Var/Var-Var
commutation. This supplies the previously missing structural target paths under
Some and swapBinders without adding a source rule.

## Source and target have different variable domains

[SourceBoundPairedPrenex](../../ExplainableCrypto/Helios/Symbolic/SourceBoundPairedPrenex.lean)
constructs a paired parallel representation for an Extended source over V and
a target over Option V. The same old Named context gets one prenex Extended
body. At the output target that body is renamed through Some, using injective
structural transport. Its name support is unchanged, so the same name-prefix
freshness conditions remain valid. Acting bodies use common base/channel
permutations that fix protected names, including the output channel.

[SourceNamedBoundPrenex](../../ExplainableCrypto/Helios/Symbolic/SourceNamedBoundPrenex.lean)
proves `BoundOutput.prenex` for every current constructor. Open-Atom uses the
already checked free-output factorization. Name Scope extends the common prefix.
Variable Scope transports the target structural path under swapBinders and
commutes its variable restriction through the name prefix. Both parallel
constructors retain the whole old context shifted through Some. Arbitrary Struct
paths compose with both endpoint representatives. The factored Extended action
has the original channel and exactly the required enlarged target domain.

`boundOutput_iff_prenex` reconstructs the original Named bound output using the
common prefix and its channel-freshness proofs. This is an actual bound-output
witness, not a silent or reflexive substitute.

[SourceFreshBoundPrenex](../../ExplainableCrypto/Helios/Symbolic/SourceFreshBoundPrenex.lean)
additionally supplies a distinct common prefix away from the output channel
and any requested finite external set. Both bodies use one name permutation,
which fixes that channel. Its interpreted corollary states that any supplied
realization of the factored Extended source yields an actual complete emitted
message and a target realized under the old environment extended with that
message. It does not assume that an environment from a different canonical
Named representative already realizes the factored source.

## Controls and remaining work

[SourceBoundPrenexSPOT](../../ExplainableCrypto/Helios/Symbolic/SourceBoundPrenexSPOT.lean)
contains twelve public kernel controls. They cover full substitution under an
injective Some map, rejection of naturality for a collapsing variable map,
Extended structural transport and an actual alpha path under variable renaming.
A bound output through both name and variable Scope factors, reconstructs and
freshens its common prefix. Parallel output retains its whole shifted old key
context; that context is distinct from the new exported binding. The two-binder
exchange commutes with further outer renaming. Private bound output remains
blocked. A complete actual-frame proof payload factors with its full raw capture.

These are general structural kernel proofs and independent controls, not a new
randomized cryptographic campaign or a security inference from failed search.
No structural/operational constructor, E equation or public observation changed.
The collapsing-map control concerns substitution naturality; it does not assert
a stronger unproved failure of every possible structural path.

The subsequent [general frame projection](helios-source-frame-projection.md)
now preserves full retained frames through structural paths and actions, with
bound-output reclosure. Next relate factored source/target realizations to
canonical environments and bodies through Named structural and alpha paths. Connect general named
observations/admissibility and outer voter nonce/let syntax, then assemble source
weak labelled bisimilarity and symbolic secrecy. Action factorization is now
available for all current step kinds, but does not itself prove canonical-frame
correspondence or solve arbitrary active constraints. General replication,
mobile channels and name creation under arbitrary plain prefixes remain outside
the current finite historical syntax.

See the [blueprint](helios-proof-blueprint.md),
[internal/free factorization](helios-source-operational-prenex.md),
[Extended bound-output interpretation](helios-source-visible-interpretation.md),
[coherent name interpretation](helios-source-name-interpretation.md) and
[task list](../../task%20list.md).

Integrated verification for the bound-output factorization checkpoint: `lake build` passes **3896 jobs**, with
**3250** nonempty standard-only and **49** axiom-free reports. The claim audit
covers **2313** public theorem entries and **97** current-status documents.
All nine changed Lean sources have current oleans; **1209** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-bound-prenex-full-build.log`.
This increment adds 31 theorem audits, including twelve public kernel controls.
Targeted controls pass 1278 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-bound-prenex-verification.txt`.

[Full Named visible interpretation](helios-source-named-visible.md) now supplies
the previously separate canonical-to-prenex visible connection for every actual
free/bound action, retaining full target interpretation. Finite-support
faithfulness is sufficient for Extended internal transport, but fixed old
environment injectivity is refuted by an alpha/dead-field control. General Named
internal correspondence, required new-frame presentation/relation invariants
and final source bisimilarity/secrecy remain open.
