# Initial-frame partial-decryption observations

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: machine-checked. In the actual initial frame, every minimum public
recipe with a `partialDecrypt` value has explicit `partialDecrypt` syntax.
Equality of two such recipes transfers between swapped worlds from equality
of their two ordered arguments, using the explicit smaller-observation premise.
The global premise, full static equivalence and final frames that publish
partial decryptions remain open.

The result covers every positive candidate count, both swaps and all valid
ground candidate representatives, including reducible representatives. This
branch needs no freshness premise. Its final interface uses the full restricted-
name policy; the origin theorem permits an arbitrary caller policy.

## Reachable values and minimum syntax

[PartialDecryptionOrigins.lean](../../ExplainableCrypto/Helios/Symbolic/PartialDecryptionOrigins.lean)
first derives actual paths from full-E equality. A fst/snd projection returning
`partialDecrypt(k,c)` must reach an argument pair whose selected member has that
value. A decryption returning that value must reach an E5 or E6 match. These
conclusions do not require literal initial matches or irreducible target fields.

The generic `EqE.passive_binary_irreducible_shape` applies to pair and
partial-decryption constructors. It identifies the exact constructor and ordered
E-equivalent components of an **irreducible** target. This premise belongs to
this shape theorem; it is not imposed on the minimum recipe's supplied value.

Tuple values, including the empty suffix, are never partial-decryption values.
Every projection chain over a tuple whose fields are neither pairs nor partial
decryptions also misses partial-decryption values. The initial ballot fields
satisfy these conditions: ciphertexts, component proofs and aggregate proofs
have distinct constructor heads. The public-key handle and its projection
chains cannot provide such values either. Thus
`Historical.General.frame_projection_not_partialDecrypt` excludes every chain
over all three initial handles, without a minimum-size premise.

[PartialDecryptionObservationInduction.lean](../../ExplainableCrypto/Helios/Symbolic/PartialDecryptionObservationInduction.lean)
combines these paths with the existing minimum pair and ciphertext origins.
A minimum projection cannot project a constructed pair, because that would
have a smaller public equivalent. The remaining pair-origin case is a handle
chain, excluded above. A successful decryption also has a smaller public
plaintext recipe and cannot be minimum. Full-E constructor separation excludes
the other heads. The resulting conclusion is exactly:

```text
∃ a b, r = partialDecrypt(a,b)
```

`minimum_partial_decryption_form` derives this syntax from minimum size and the
supplied first-world E-value. It assumes no origin certificate or minimum size
in the other world.

## Ordered equality transfer

Full-E partial-decryption injectivity reduces constructor equality to both
ordered component equalities. Each component pair is public and strictly
smaller than the sum of the original constructor sizes.
`partial_decryption_equality_transfer` applies `Frame.ObservationsBelow` to
these two comparisons; its frames can be arbitrary frames with three handles
and the same name policy.

`Historical.General.minimum_partial_decryption_equality_swap` derives both
constructor forms in the actual initial frame and applies that transfer. Its
premises are two first-world minimum full-policy recipes, a supplied
partial-decryption E-value for each, and `ObservationsBelow` at their total
node count. No second-world value or minimum-syntax preservation is assumed.
This conditional branch does not discharge the smaller-observation premise.

## Claim ledger

Names below are under `ExplainableCrypto.Helios.Symbolic`; `General` abbreviates
`Historical.General`.

| Claim | Evidence | Declaration | Scope |
| --- | --- | --- | --- |
| Passive binary normal values preserve ordered fields | machine-checked | `EqE.passive_binary_irreducible_shape` | Pair or partialDecrypt, irreducible target |
| A partial-decryption-valued projection reaches a pair | machine-checked | `EqE.projection_partialDecrypt_inversion` | fst/snd, arbitrary target fields |
| Such a decryption reaches E5 or E6 | machine-checked | `EqE.decryption_partialDecrypt_inversion` | Actual `DecryptionMatch` in the conclusion |
| Initial handle chains expose no partial-decryption value | machine-checked | `General.frame_projection_not_partialDecrypt` | All three handles, both swaps, all valid candidates |
| A minimum partial-decryption value has constructor syntax | machine-checked | `General.minimum_partial_decryption_form` | Arbitrary caller policy, initial frame only |
| Equality transfers from two smaller ordered tests | machine-checked | `General.minimum_partial_decryption_equality_swap` | First-world minima/values and explicit bounded premise |

## Independent controls and executable gate

[PartialDecryptionObservationSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/PartialDecryptionObservationSPOT.lean)
contains eight theorem controls. A constructor with two public literal names
is an exact three-node minimum, for arbitrary valid candidate assignments in
the two-candidate fixture. The proof excludes every smaller public recipe using
the general origin theorem, including all handles and unbounded literal names.
A projection wrapper has the same value but neither constructor syntax nor
minimum size, preserving the omitted-minimum counterexample.

The ordered-field control fixes the endpoint as `partialDecrypt(40,50)` even
when both arguments are projection wrappers. Reversing the names gives an
unequal value. The E6 binding control decrypts a matching ciphertext to zero;
changing only its nonce from 60 to 61 changes the corresponding partial-
decryption constructor value. This control does not assert a theorem about
all nonmatching E6 decryption attempts.

Three delayed paths produce the independently specified partial-decryption
output: a pair revealed by projection, an E5 key revealed by projection, and an
E6 partial-decryption argument revealed by projection. Each has an actual match
in the checked conclusion. Projecting an honest ciphertext field cannot expose
a partial-decryption value.

An artificial one-handle frame publishing `partialDecrypt(40,50)` refutes the
origin theorem with its initial-frame premise removed: its public handle is a
one-node minimum without constructor syntax. This frame is a premise control,
not an implementation of the historical final frame. The complete induction
interface is also inhabited by unequal three-node constructor recipes with a
six-node total bound. Diagonal candidate assignments supply its bounded premise
without assuming static equivalence of different votes.

`PartialDecryptionObservationExperiments.lean` runs two deliberately broken
gates first. Argument commutation and omitted minimum size both fail at input
0, seed 1, with zero shrinks; the controls above preserve these counterexamples.
The two positive gates pass seeds 1, 7 and 42, each with 500 configured cases,
maximum size 40 and `gaveUp=0`, plus 256 deterministic inputs.

A separate 2400-input sweep covers all three handle roots and every fst/snd word
through length four, at one through five candidates and both swaps. Shorter
chains repeat, so this is not a count of distinct chains. The generated honest
assignments are left abstention and right selection of candidate zero. The
constructor gate fixes ordered public names independently of the normalizer.
These tests use raw normalization on the stated families; they do not decide
full E or prove arbitrary-recipe privacy.

## Reproduction and remaining work

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/PartialDecryptionObservationExperiments.lean
lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean
python3 scripts/check_helios_claims.py
```

The full build passes (3478 jobs), including 19 new public theorem type/axiom
checks and five definition checks. Its 1233 nonempty axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`; 17 further reports are axiom-free.
No warnings, errors or `sorryAx` occur. The local log is
`tmp/variable-overlap/partial-decryption-observation-full-build.log`.
The source audit checks 264 public theorem entries and selected stale claims
in 16 current-status documents; it does not replace elaboration or establish
log freshness.

Trusted definitions remain E/E0, public recipes, node-count minimality, tuple
projections, general frames and the existing full-E paths and injectivity.
The reality oracle is Appendix B.3 of the historical source: Lemma 10's initial
frame publishes the key and ballots, whereas Lemma 12 additionally publishes
partial decryptions. E6 binds the ordered key and complete ciphertext. No
cryptographic equation, public operation, custom axiom or confluence assumption
changed.

The subsequent [pair-valued branch](helios-pair-observations.md) now handles
constructed pairs and nonempty ballot tails under the same bounded premise.
Other value heads and transport of arbitrary recipe evaluations must still
establish the global smaller-observation premise. Final partial-decryption
frames and historical process matching remain separate obligations in the
canonical [task list](../../task%20list.md). See the earlier
[public-key branch](helios-public-key-observations.md) and
[static-equivalence interfaces](helios-static-equivalence.md).
