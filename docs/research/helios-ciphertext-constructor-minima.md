# Minimum constructed ciphertexts

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. In the actual initial historical frame, a ciphertext
constructor with three minimum public children is itself minimum. The result
covers every positive candidate count, valid ground candidate substitutions,
and either assignment under the full name restriction. It does not require
freshness, normality or preservation of smaller observations.

## Account for the selected key

`CiphertextAssembly.key_group_budget` proves
`keyRecipe.nodeCount + group.budget ≤ recipe.nodeCount + 1` for every assembly.
The earlier grouping budget accounted for public nonce and payload observations.
The new bound also retains the selected key's full syntax size.

For a constructed group with nonce `r` and payload `p`, its budget is
`r.nodeCount + p.nodeCount + 2`. The new bound therefore ensures that the
regrouped ciphertext built from the selected key, `r` and `p` fits within the
original assembly's node count. This holds for repeated keys, reducible key
recipes and arbitrary multiplication trees. No semantic hypothesis is needed
for the size bound.

## Exclude honest contributions to a public nonce

`CiphertextGroup.constructed_of_public_nonce` proves that a group whose nonce
is E-equal to a nonce-public recipe must be constructed. An honest group
retains at least one restricted honest nonce factor. A mixed group retains
such a factor alongside its public contribution. Restricted-factor
non-deducibility excludes both cases.

The theorem needs no freshness premise: retaining one protected factor is
enough, even when honest nonce names collide. Publicness of the proposed nonce
recipe is essential. The group need not be independently supplied as public
for this exclusion theorem.

## Minimum ciphertext constructor

`minimum_penc_of_children` chooses an arbitrary minimum equivalent of the
constructed ciphertext. The existing origin theorem supplies a ciphertext
assembly and its exact key, nonce and message E-values. The source constructor's
nonce is public, so the assembly has a constructed group. Its grouped public
nonce and payload and its selected key are competitors for the original
minimum children.

Each original child therefore costs no more than its grouped competitor.
The key-plus-group bound shows that their ciphertext constructor costs no
more than the chosen minimum equivalent. It is consequently minimum itself
and is its own shared representative in every destination frame under the same
policy. This does not assert that its evaluated ciphertext value is unchanged
when honest votes change.

`crypto_transport_of_destructor_arithmetic` supplies this closure to the prior
local-root interface. `Frame.DestructorArithmeticRootTransport` retains only
successful decryption, successful proof checking, multiplication, addition and
composition for nonminimum roots with minimum children.
`staticEq_of_destructor_arithmetic_transport` derives initial-frame static
equivalence if these remaining obligations hold in both orientations. The
criterion still needs fresh names through the earlier projection and pairing
results. The subsequent [composition minimum result](helios-composition-minima.md)
discharges compose. Successful decryption/checking, addition and multiplication
remain unproved for different votes.

## Controls and evidence

Seven public SPOTs retain:

- An 11-node fused ciphertext with a four-node selected key. It exceeds the
  old component budget of 8 while fitting the original 12-node assembly, and
  its value agrees with that assembly in both assignments.
- An exact 16-node minimum ciphertext with non-atomic minimum key and proof
  children, shared with any destination frame under the same policy.
- A minimum public ciphertext in a frame with colliding honest nonces,
  confirming that freshness is absent from this constructor closure.
- A removable nonce wrapper giving a smaller public ciphertext when the child
  minimum premise is dropped.
- An arbitrary frame directly publishing a public ciphertext: its three
  literal children are minimum, but the ciphertext has a shorter handle.
  The closure theorem is specific to the initial historical frame.
- Direct naming of a restricted nonce, which matches an honest group and
  refutes group exclusion without publicness.
- A diagonal instantiation of the reduced criterion with distinct public
  names. This is not a different-vote privacy theorem.

The pre-proof Plausible gate detects omitted child minimum and omitted key
budget at input 0, seed 1, zero shrinks. Positive checks vary wrapped key sizes,
constructed multiplication trees, honest and mixed groups, and E-equivalent
common keys. They check the key-plus-group size bound for five assembly forms
and public-only fusion values in both swaps. Seeds 1, 7 and 42 pass 500
configured cases each, size 40, `gaveUp=0`; all 2048 backstop inputs pass.
These tests compare raw normal forms and syntax sizes. They do not establish
unbounded minimum size or decide arbitrary full E equality.

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/ConstructedCiphertextExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/constructed-ciphertext-full-build.log
```

The four new modules are `ConstructedCiphertextMinima`,
`DestructorArithmeticTransport`, `ConstructedCiphertextExperiments` and
`ConstructedCiphertextSPOT`. The audit checks twelve public theorem types and
axiom sets, including seven controls, and three definition interfaces. The full
build passes (3555 jobs), with 1547 nonempty axiom reports using only propext,
Classical.choice and Quot.sound, and 18 axiom-free reports. No warnings, errors
or sorryAx occur. The claims checker covers 579 public theorem entries and
32 current-status documents. The
[results ledger](helios-results.md#constructed-ciphertext-minimum-enquiry)
records the full build evidence.

Trusted definitions remain E/E0, the actual candidate frames and public-name
policy, protected nonce factors, grouping, node count and minimum recipes. The
independent semantic reference is E7's common-key fusion and preserved nonce
factors. No cryptographic equation, public operation, confluence premise or
custom axiom changes. Successful destructor, addition and multiplication transport, final
public partial decryptions, process matching and full ballot secrecy remain
open in the [task list](../../task%20list.md).
