# Private channels through structural closure

B9 now proves that every free or bound-variable visible action from an actual
restricted state uses a public channel, even through arbitrary current
structural/alpha derivations. Every operational step can only remove free
static channels, and hidden-channel actions remain blocked after any finite
internal execution. These are machine-checked converse obligations for channel
policy. They do not complete the payload/input/target converse or symbolic
secrecy. B9/B10 remain at 8/10 unweighted milestones (80%).

## Static channel support

[SourceChannelSupport.lean](../../ExplainableCrypto/Helios/Symbolic/SourceChannelSupport.lean)
computes channel support for plain agents and extended processes. It includes
every prefix in every continuation and conditional branch, so membership alone
does not establish that an action is currently enabled. Base-term substitution,
input binding and variable renaming leave these channels unchanged. Name
mapping transports them under the channel map, independently of base names.
Channel support agrees with the channel-sorted part of syntactic name support.

Every existing extended structural rule preserves channel support. Active
substitution and full E Rewrite affect base terms and cannot change static
channels. Both free actions and bound outputs must use a channel present in
their source; these proofs include arbitrary extended structural closure.

## Named structural invariance

[SourceNamedChannels.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNamedChannels.lean)
removes the bound channel at a channel restriction and leaves channel support
unchanged at a base-name or variable restriction. Its support is exactly the
channel-sorted part of `Named.freeNames`, and free names are contained in
`allNames`. Typed variable renaming preserves channels, while channel permutations
map them bijectively.

`Named.Structural.channels` covers every structural constructor: embedded active
rules, parallel/context rules, restriction exchange, extrusion and both alpha
rules. Freshness in channel New-Par permits distributing binder removal through
parallel composition. A fresh channel alpha swap preserves free channels after
replacing the old binder with the new one. Freshness cannot be dropped; a
retained finite-set counterexample shows the resulting capture changes free
channel support.

## Visible-action converse and persistence

[SourceChannelScope.lean](../../ExplainableCrypto/Helios/Symbolic/SourceChannelScope.lean)
proves that every named free/bound output action uses a free source channel.
The proof handles Struct using structural support invariance and Name Scope
using its actual label-freshness premise. Actual active frames contain no static
channels: their complete values are base terms. The exact restricted-state
support consists of channels in its body that are absent from the hidden set.

`restricted_free_channel_public` and `restricted_bound_channel_public` therefore
recover the public-channel premise from arbitrary named derivations and targets.
The private-channel blocking corollaries exclude both directions of visible
interaction on hidden channels. They strengthen the earlier direct Scope
freshness controls by quantifying over the entire current structural closure.

[SourceChannelPreservation.lean](../../ExplainableCrypto/Helios/Symbolic/SourceChannelPreservation.lean)
proves support inclusion for internal, free and bound-output steps in both
extended and named syntax. The fresh variable introduced by bound output does
not introduce a channel; its context shift and binder exchange preserve channel
support. Internal closure preserves inclusion over any finite reduction sequence.
`after_internal_private_free_blocked` and `after_internal_private_bound_blocked`
exclude private actions after arbitrary such sequences. These results allow
internal communication on private channels and public output of secret-bearing
base values.

## Controls and limits

[SourceChannelClosureSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceChannelClosureSPOT.lean)
has twelve kernel controls. They exclude private input/output after arbitrary
structural rearrangement, check a fresh alpha-renamed private output, and expose
the capture error when alpha freshness is dropped. Public secret output and
private internal communication remain possible. Private output is excluded
after arbitrary internal execution; actual election trustee/honest channels are
covered at every stage, with no reachability assumption needed for this policy
property.

Two negative generalization controls retain the exact boundaries. Taking a
conditional branch can remove channels, so operational preservation is inclusion,
not equality. A raw inverse-projection Rewrite adds a base name while leaving
channels unchanged, so this is not invariance of all syntactic free names.
The full E theory and all public cryptographic observations remain intact.

## Input alpha-representative boundary

[SourceInputAlphaBoundary.lean](../../ExplainableCrypto/Helios/Symbolic/SourceInputAlphaBoundary.lean)
refutes a tempting stronger converse: a recipe on an arbitrary alpha-closed
source input need not be public under the original fixed base-name policy.
The checked example retains a private-key active binding and a receiver with
well-formed variable/active syntax. Alpha conversion changes the private binder
and key occurrence from 40 to fresh 41. Input literal 40 can then pass Scope,
and the resulting process retains key pk(41) while forwarding the received 40.
Literal 40 is forbidden by the original policy {40}, and permitted by {41}.
Four additional kernel proofs check well-formedness, the exact alpha change,
the input derivation and the two policy answers.

This is a counterexample to the fixed-representative proof interface, not an
attack on the election or a disclosure of the bound key. The source alpha rule
and full input semantics are unchanged. The subsequent
[fresh-representative construction](helios-source-fresh-names.md) now supplies
coherent canonical policies for both worlds, preserving input labels and full
frame observations. The remaining full derivation/target converse must use
those fresh representatives. The
channel converse above remains valid: alpha cannot introduce a new free static
channel, whereas an input may receive a new free base-name literal.

The current syntax has fixed static channels and base-valued messages. This
result does not address mobile channel communication or arbitrary name creation
under prefixes. The remaining source converse must still recover public input
recipe scope modulo fresh bound-name representatives, actual payload/continuation behavior and output captures from
arbitrary named structural/alpha derivations. Named-frame observations,
admissibility and outer voter nonce/let construction remain required before
weak labelled bisimilarity and full symbolic secrecy. No new randomized
cryptographic campaign was run, and no full privacy claim follows from these
channel-policy results.

See the [blueprint](helios-proof-blueprint.md),
[explicit name restrictions](helios-source-name-restrictions.md),
[renamed observations](helios-source-renamed-observations.md) and
[stage matching](helios-process-stages.md).

Integrated verification for the channel-closure/alpha-boundary checkpoint: `lake build` passes **3852 jobs**, with
**2996** nonempty standard-only and **47** axiom-free reports. The claim audit
covers **2057** public theorem entries and **91** current-status documents.
All eight changed Lean sources have current oleans; **1120** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-channel-closure-full-build.log`.
This increment adds 54 theorem audits, including twelve channel controls and
four alpha-input boundary proofs, plus four definition checks. Targeted channel
controls pass 1222 jobs; the final full build also checks the boundary module.
Freshness/hole/link evidence: `tmp/variable-overlap/source-channel-closure-verification.txt`.
