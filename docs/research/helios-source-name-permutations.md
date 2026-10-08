# Name permutations in the source fragment

B9 now has machine-checked global name-permutation equivariance for the current
finite static-channel, variable/active process fragment. Base names and channel
names have independent permutations. Input variables, restricted variables and
active-substitution domains retain their identity. Full E equality and
disequality, internal reductions and labelled actions are preserved and
reflected. B9/B10 remain incomplete at 8/10 unweighted milestones.

This supplies a prerequisite for fresh name allocation. It does not implement
name restriction, prove bound-name alpha-equivalence, or discharge the full
source operational converse. Global renaming and changing a bound name inside
its scope are different obligations.

The later [explicit restriction bridge](helios-source-name-restrictions.md)
adds sorted name binders, fresh alpha rules and forward scoped-step derivations.
Its full structural/alpha converse and named observations remain open.

## Terms, observations and binding

[SourceNameTerms.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameTerms.lean)
maps every literal name in every term position, including structured keys,
nonces and all four proof arguments. Variables and operators stay fixed. The
map commutes with arbitrary variable substitution and has an inverse for
permutations. Every generating E equation and its congruence closure transport
under arbitrary name maps; equality reflection uses the inverse permutation.
No new equation, normalization oracle or cryptographic assumption is added.

`Term.public_mapNames_iff` moves the restricted-name policy along with the term.
Keeping the old policy can accidentally make a secret literal public. This
theorem addresses recipe publicness. The subsequent
[renamed-observations bridge](helios-source-renamed-observations.md) now supplies
a Frame/ScopedState interface, full static-equivalence transport/reflection and
every evaluated scoped step under consistently renamed policies.

[SourceNameProcesses.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameProcesses.lean)
extends the map to equality/disequality/conjunction guards and plain processes.
Guard truth is preserved when variable values are renamed consistently. The
process map changes every channel using the channel map and every payload using
the base-name map. These are separate sorts even when their numeric indices
coincide. Substitution, input binding and shifts commute with name mapping,
including beneath nested input binders.

## Behavior and active substitutions

[SourceNameBehavior.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameBehavior.lean)
transports parallel structural congruence, core internal reduction, internal
reduction modulo parallel congruence, payload events and visible actions.
`CoreStep.mapNames_iff`, `Tau.mapNames_iff` and `Visible.mapNames_iff` give both
directions for independent permutations. Negative guards require equality
reflection. A channel collision can introduce a communication, so arbitrary
noninjective maps are not used to reflect behavior.

[SourceNameExtended.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameExtended.lean)
maps plain processes, parallel components, variable restrictions and active
substitution payloads. Variable domains remain unchanged. Name mapping commutes
with variable renaming, including insertion of a fresh variable. Every current
structural rule transports: Alias, fresh New-Par, active substitution into a
plain process and full-E Rewrite. Internal reduction transports through its
atomic communication, ground conditional and structural/context rules.
`Structural.mapNames_iff` and `Reduction.mapNames_iff` reflect these relations
under permutations.

[SourceNameLabels.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameLabels.lean)
transports free inputs, free variable outputs and bound variable outputs.
Input payloads and channels move; an output's variable stays fixed. Bound
output still exchanges the two variable binders when crossing a variable
restriction and shifts an untouched parallel context. `FreeStep.mapNames_iff`
and `BoundOutput.mapNames_iff` cover arbitrary derivations in this fragment.
The forward structural/free/bound-output maps admit arbitrary name maps; their
reflection theorems require permutations.

## Independent controls and limits

[SourceNameSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SourceNameSPOT.lean)
has twelve kernel controls. Independently written expected syntax checks
separate base/channel/variable sorts and every nested proof field. Structured-key
homomorphism and full-ciphertext partial decryption move correctly. A concrete
private election handshake and a bound output crossing a variable restriction
exercise actual earlier derivations. Negative controls retain the changed
policy requirement, blocked one-endpoint renaming, omitted payload renaming,
and full-E equality/disequality changes under a constant name map. A permutation
preserves the negative guard that the constant map invalidates.

These are structural proofs and kernel controls, with no new randomized
cryptographic campaign. They neither infer secrecy from a blocked attack nor
replace the remaining source restrictions, alpha-equivalence, outer voter
construction, full operational converse and final weak bisimilarity obligations.
See the maintained [blueprint](helios-proof-blueprint.md),
[well-formedness record](helios-source-wellformed.md) and
[results ledger](helios-results.md).

Integrated verification for the global name-permutation checkpoint: `lake build` passes **3837 jobs**, with
**2880** nonempty standard-only and **47** axiom-free reports. The claim audit
covers **1941** public theorem entries and **88** current-status documents.
All eight changed Lean sources have current oleans; **1090** local links resolve.
No proof holes, custom axioms, warnings or errors were found; `git diff --check`
passes. Log: `tmp/variable-overlap/source-name-permutation-full-build.log`.
This increment adds 55 theorem audits, including twelve kernel controls, and
six definition checks. Targeted controls pass 1213 jobs. Freshness/hole/link
evidence: `tmp/variable-overlap/source-name-permutation-verification.txt`.
