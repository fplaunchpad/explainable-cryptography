# Active substitutions and derived atomic communication

B9 now derives the evaluated internal rules from explicit atomic communication,
active substitutions and fresh variable scope extrusion. Local active lets
eliminate to capture-avoiding process binding; arbitrary messages can therefore
be communicated through fresh atomic variables. Every existing internal Tau
and historical internal stage transition has such a derivation. Exported active
variables survive every structural rewrite and internal reduction in this
fragment. These are machine-checked supporting results. The full source
converse and name-scope bridge remain open, so B9/B10 remain incomplete
at 8/10 milestones (80%, unweighted).

## Explicit source rules

[SourceExtendedSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedSyntax.lean)
defines extended syntax for plain finite Agents, parallel composition, variable
restriction and active substitutions. A restricted variable is `None`; every
outer variable is shifted through `Some`. `letTerm m p` is the source's
`νx.({m/x} | p)` with a fresh binder, including the shift of all variables of m.

`Extended.Structural` contains explicit Par-0/A/C, variable New-Par, Alias,
Subst and EqE Rewrite constructors, their equivalence closure and parallel/
variable-restriction evaluation contexts. `plainPar` connects the two syntax
presentations of parallel plain processes. New-Par inserts Some into the
outside process, enforcing that it does not mention the fresh variable.
Alias removes a restricted definition whose right-hand side is independent of
that variable. [General active substitution](helios-source-general-substitution.md)
now adds the active-active Subst case and derives substitution through every
current Extended context. Arbitrary Named contexts use fresh representatives
to avoid capture of the provider payload; the retained provider and all active
domains remain explicit.

`Extended.Reduction` has atomic variable Comm, ground semantic Then/Else,
evaluation contexts and structural closure. Atomic Comm sends a variable; its
receiver binder is renamed to that variable, expressed by `Agent.bind (.var x)`.
There is no primitive arbitrary-message communication constructor in this
relation. Ground formulas retain the full E interpretation.

These definitions are a variable/active fragment, not the full extended source
calculus. Name restriction, replication, variable-valued channels, New-C,
and their full structural closure are not yet implemented here. Variable-labelled
Out-Atom/Open-Atom/Scope rules now exist in SourceAtomicLabels, and the evaluated
output/active-frame bridge is proved in SourceOutputDerivation. Raw extended syntax also permits invalid multiple definitions;
a separate variable well-formedness predicate now rejects them and is certified
for actual canonical frames, ground lets, raw outputs and their step targets.
Full source admissibility remains part of the name-scope/converse bridge.
The fresh local lets used in the communication derivation introduce exactly
one definition for their newly restricted variable and no exported definition.

## Derived communication and actual election steps

[SourceActiveBinding.lean](../../ExplainableCrypto/Helios/Symbolic/SourceActiveBinding.lean)
proves that shifting then binding restores a whole process, that substituting
its fresh active variable agrees with binding, and that an atomic relay followed
by evaluating that variable is exactly the original input substitution. All
three laws include arbitrary nested input binders and existing outer variables.

`let_eliminate` is an explicit chain: Subst distributes the message into the
plain continuation, New-Par extracts the now-independent continuation, Alias
removes the restricted substitution, and Par-0 removes the empty process.
`output_factor` uses this equivalence backwards to factor an arbitrary output
message into a fresh active variable.

`message_communication` places both sender and receiver under that fresh local
let, applies atomic Comm in its evaluation context, then eliminates the let.
The result is exactly the old sender continuation in parallel with the receiver
bound to the complete original message. This derives the evaluated rule rather
than making it an axiom or adding it as a primitive. `coreStep_derivable` also
covers ground conditionals and all existing parallel core contexts.

[SourceExtendedInternal.lean](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedInternal.lean)
derives every existing ParEq from the extended structural rules. It combines
that with the core derivation to prove `tau_derivable` and
`residual_internal_derivable`. Thus all private honest/trustee communications
and accepted/rejected guard steps already proved for the election have explicit
atomic/active derivations. These statements prove the forward direction;
arbitrary extended reductions are not yet classified by a converse theorem.

## Export preservation and controls

[SourceExtendedExports.lean](../../ExplainableCrypto/Helios/Symbolic/SourceExtendedExports.lean)
defines the exported-variable observation recursively through restriction and
proves it is preserved by injective renaming, structural equivalence and internal
reduction. A free active substitution cannot become a plain process, even if
its variable is unused. Alias removes only the restricted variable. This is an
export-domain invariant, not static equivalence of the full payload frame and
not a replacement for the source's unique-definition requirement.

Ten controls in
[SourceActiveBindingSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceActiveBindingSPOT.lean)
use a compound message containing an old variable and a continuation with a
newer input binder. An independently written result distinguishes the local
let value, new input value and old variable in separate output positions. The
binding law and active-let derivation reach that exact result, while a capturing
mutant is unequal. The compound-message handshake has an atomic/active
derivation. Restricted aliases disappear, exported aliases cannot disappear
through either structural equivalence or reduction, and fresh scope extrusion
retains an old exported variable. Actual first-honest communication and replay
rejection also instantiate the derived election rules.

The reality oracle is the active-let paragraph following Figure 2 and the
Comm/Alias/Subst/New-Par rules of Figure 3 in Cortier–Smyth. These are structural
proofs and kernel controls; no new randomized security campaign is claimed.
The atomic output and recipe-input bridges are now checked, and internal steps
also derive beside actual public active frames. Next extend name scope/alpha
and prove the required converse and outer voter construction correspondence,
using the now-proved variable well-formedness certificates,
then combine [visible correspondence](helios-source-visible.md),
[internal matching](helios-source-internal.md) and observations into source weak
labelled bisimilarity. The [blueprint](helios-proof-blueprint.md) and
[task list](../../task%20list.md) keep the full secrecy objective open.

Integrated verification for the active-internal checkpoint: `lake build` passes **3816 jobs**, with
**2720** nonempty standard-only and **42** axiom-free reports. The claim audit
covers **1776** public theorem entries and **84** current-status documents.
All eight changed Lean sources have current oleans; **1050** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-active-full-build.log`. This increment
adds 28 theorem audits, including ten kernel controls, and eight definition
checks. Targeted controls pass 1189 jobs. Freshness/hole/link evidence:
`tmp/variable-overlap/source-active-verification.txt`.

[General local-definition elimination](helios-source-local-normalization.md) now
extends the plain-process let derivation through Extended contexts and fresh
Named representatives. The provider is independent of its own local binder;
unique definitions discharge the no-redefinition condition.

[Explicit voter computation](helios-source-voter-computation.md) now compiles
two local lets per candidate and four aggregate lets into this same source
syntax. Their structural elimination yields the exact historical ballot and
retains the complete proof fields. The later scope increment connects their
interleaved nonce restrictions to the complete initial election.

[Board tally computation](helios-source-board-tallies.md) now compiles finite
local definitions with arbitrary plain continuations. Finite pointwise-E
environment substitution has an actual structural path, including uses beneath
future inputs. This supplies the direct-register/tuple-projection bridge for
board results without extending the structural rules.

[Interleaved voter scopes](helios-source-voter-scopes.md) compile to the existing
Named name/variable constructors. Their whole-election path uses the existing
New-Par/New-C and unused-name rules; it introduces no structural constructor.

[Open election application](helios-source-voter-application.md) extends the
instantiation graph through Named syntax with explicit name freshness and
variable-valued active domains. The actual key export is preserved; no new
source structural or reduction rule is introduced.
