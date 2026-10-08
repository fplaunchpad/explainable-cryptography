# Expanded ciphertext keys and forward value transport

Status: machine-checked, conditional on smaller public equality observations.
This B8 dependency retains a public recipe for a ciphertext's key across the
vote swap. The key recipe is strictly smaller than the ciphertext recipe.
Its ground value may change between frames. The result supplies ciphertext
values in the destination, not equality of their messages or nonces across
assignments.

## Public statements and dependencies

[CiphertextKeyTransfer.lean](../../ExplainableCrypto/Helios/Symbolic/CiphertextKeyTransfer.lean)
proves `Frame.ciphertext_syntax_key_transfer` for arbitrary frames with the same
handle count and public-name policy. It uses the existing
`CiphertextRecipeSyntax`: constructors, projection chains and products.
For each ciphertext-valued selected leaf, the caller must supply a smaller
public key recipe, its source key equality and a destination ciphertext under
that recipe. For the whole public recipe `r`, the caller supplies
`ObservationsBelow φ ψ r.nodeCount` and a source ciphertext value.

The conclusion is an actual recipe `k`, its publicness, the strict bound
`k.nodeCount < r.nodeCount`, source equality to the supplied key, and a
destination ciphertext whose key is `ψ.eval k`. The same source recipe cannot
satisfy the strict witness bound. The theorem does not equate `φ.eval k` with
`ψ.eval k`.

At a product, full-E inversion gives ciphertext values for both children with
the same source key. Their inductively obtained key recipes have total size
strictly below the product size. The observation premise transports their
equality; the existing homomorphic law then combines the destination values.
This reuses the existing equational model and inversion lemmas. It introduces
no new grouping representation or homomorphic equation.

[ExpandedCipherKeyTransfer.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedCipherKeyTransfer.lean)
discharges the selected-leaf premise for the actual expanded publication:

- `expanded_projection_ciphertext_key_transfer` classifies the leaf using
  numeric source results. It retains the one-node election-key handle and
  uses the same honest tuple position in the destination. It needs no
  observation premise.
- `expanded_ciphertext_syntax_key_transfer` instantiates the generic induction.
- `expanded_minimum_ciphertext_key_transfer` obtains the syntax from the
  existing minimum ciphertext origin theorem.
- `accepted_expanded_minimum_ciphertext_key_transfer` obtains numeric results
  from fresh names and sequentially accepted public submissions.
- `accepted_expanded_minimum_ciphertext_value_transfer` exposes the forward
  ciphertext-value consequence under the same accepted-election, source
  minimum and smaller-observation premises.

Both swap parameters are arbitrary. Source minimum size is required only by
the minimum interfaces. Source numeric results are explicit until acceptance
discharges them; no destination numeric premise is needed for forward transfer.
The smaller-observation premise remains unproved globally for B8.

## Controls and refutation gate

[ExpandedCipherKeySPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedCipherKeySPOT.lean)
retains six checked controls:

1. An actual accepted size-two minimum honest selector has a size-one public
   key witness in either swap direction. Its observation budget admits no
   tests because every recipe has positive size.
2. A product uses a key constructed from published partial and result handles
   and a reducible projection alias. The syntax theorem supplies its strictly
   smaller public key witness in a diagonal election, where observations agree.
3. Ciphertexts under distinct named keys cannot fuse under full E.
4. Raw-unequal but E-equal keys fuse, retaining the explicit combined nonce
   and plaintext. This preserves the minimized raw-equality mutation.
5. In a two-handle frame, equal source keys and unequal destination keys give
   a public ciphertext product only in the source. The required smaller
   observation premise is explicitly false.
6. A repeated ciphertext factor contributes twice to the nested nonce and
   plaintext combinations under the existing homomorphic equation.

The expected fusion rule and selector key come from the historical symbolic
model, with keys and repeated factors chosen independently of normalization.
The two-handle countermodel tests necessity of an abstract transport premise;
it is not an attack against the actual expanded election frames.

[ExpandedCipherKeyExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ExpandedCipherKeyExperiments.lean)
checks executable ciphertext shapes for nested published keys, raw projection
aliases, honest leaves and repetitions. Both known-false properties fail at
input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 cases at size 40
with `gaveUp=0`; 2048 deterministic inputs pass, covering both candidates and
assignments. These checks concern raw-normalizer outputs on this generated
family; the general full-E key witnesses are supplied by the proofs, not by
the campaign. `normalizeRaw` is not a full-E decision procedure.

## Verification and remaining scope

The generic target passes 824 jobs, the expanded target 931 jobs and all six
controls 1033 jobs. The initial control elaboration failures concerned an
implicit recipe and unfolding publicness of a local key; the statements and
equational model were unchanged. Twelve new public theorem type/axiom audits
are integrated in [Audit.lean](../../ExplainableCrypto/Helios/Symbolic/Audit.lean).
Full build verification is recorded in the [results ledger](helios-results.md).

This supplies forward ciphertext-value transport for the later B8 decryption
argument. [General value-shape reflection](helios-expanded-value-shapes.md) is
now checked using these witnesses, and result-handle probes close syntactic
minimum-decryption equality, including borrowed E6. [Expanded stuck values](helios-expanded-stuck-values.md)
now supply arbitrary stuck-destructor origins and equality. The
[assembly theorem](helios-expanded-ciphertext-assemblies.md) now derives the
original-size ciphertext comparison bounds and closes conditional ciphertext
equality. Remaining shared minima and global induction are open.
The [blueprint](helios-proof-blueprint.md) remains at B8, seven of ten completed
milestones (70% unweighted coverage). B9 historical process matching and B10
full symbolic secrecy remain open.
