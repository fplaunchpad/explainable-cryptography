# Expanded-frame value origins and partial equality

Status: **machine-checked minimum origins and conditional partial-value
transport**. Pair and ciphertext origins now cover arbitrary nested minimum
recipes in the expanded frame when its result values are numeric. Accepted
public elections discharge that condition. Minimum partial-valued recipes are
explicit constructors or published partial handles. Their equality branch and
constructed-partial minimum closure are also checked. B8's complete
cross-world observation theorem remains open.

## Reusing the ciphertext-product proof

`Frame.minimum_pair_and_ciphertext_origins` extracts the existing simultaneous
induction into a reusable theorem. It has two substantive frame premises:
no atomic handle has a ciphertext value, and every ciphertext-valued projection
chain has a `CiphertextProduct` certificate. The certificate supplies a strictly
smaller public plaintext recipe. Both the grammar and its size/soundness proofs
are reused unchanged.

`ExpandedResultsNumeric` records numeric values of the actual result slots.
`accepted_expanded_results_numeric` derives it for either assignment from fresh
names, public submissions and chronological source acceptance. The lower-level
origin results keep this condition explicit and preserve the caller's public
name policy; they do not silently assume that arbitrary frames satisfy it.

`expanded_handle_not_ciphertext` and `expanded_projection_ciphertext_origin`
discharge the generic frame premises. The three old handles keep their existing
meanings. Partial handles are neither ciphertexts nor extractable pairs;
numeric result handles cannot produce ciphertext selectors. Every
ciphertext-valued chain is therefore an actual indexed honest ballot component.
Its candidate value is E-equal to a literal bit in the supplied world, yielding
the existing constant-leaf certificate with the original selector's size bound.
The literal-bit witness here may depend on the world; this is not a claim of
shared adversarial ballot reconstruction.

## Full minimum origins

`expanded_minimum_pair_and_ciphertext_origins` instantiates the generic induction
with these proved premises. Its corollaries supply pair origins, ciphertext
syntax, and an actual public plaintext recipe with a strict size bound and
both target component equations. No certificate is assumed from the caller.

`expanded_minimum_decryption_no_match` excludes both E5 and E6 matches for a
whole minimum decryption recipe. A successful match would expose the smaller
public plaintext recipe supplied by its ciphertext argument. Ordinary public
decryption still works; the controls exhibit successful E5/E6 recipes that
therefore cannot be minimum. `accepted_expanded_minimum_decryption_no_match`
discharges the numeric-result condition from the actual election assumptions.

`expanded_projection_partial_origin` proves that a partial-valued selector
chain stops at an individual published partial handle. The old ballot fields
cannot supply partial values, and neither a partial nor a numeral can expose
pair fields. Combining this with pair origins and the decryption no-match
result gives `expanded_minimum_partial_decryption_form` for arbitrary target
keys and bindings: explicit partial constructor or published partial handle.
`accepted_expanded_minimum_partial_form` applies it directly to accepted
public elections with no remaining origin/certificate premise.

## Partial-value equality and minimum closure

The existing `partial_decryption_equality_transfer` lemma now works for any
handle count, preserving its two strictly smaller public argument comparisons.
Its old three-handle callers retain the same behavior and are rebuilt.

`expanded_minimum_partial_equality_swap` covers all pairs of source-world
minimum partial values:

- Constructed/constructed equality transfers through smaller argument tests.
- Constructed/borrowed equality is impossible in either world: it would expose
  a public recipe for the restricted election secret.
- Borrowed/borrowed equality reduces to full aggregate-binding equality and
  transfers through the already-proved initial-frame equivalence.

The smaller-observation premise remains explicit. The global induction that
supplies it in the expanded frame is not yet closed.
`expanded_minimum_partial_of_children` separately proves that an explicit
partial with minimum children is minimum. The full origin theorem handles
arbitrary competitors; restricted-secret non-deducibility excludes a shorter
borrowed-slot alias. It assumes public submissions and numeric result values.

## Evidence and controls

Artifacts:

- [Generic origin induction](../../ExplainableCrypto/Helios/Symbolic/FrameMinimumOrigins.lean).
- [Expanded projection origins](../../ExplainableCrypto/Helios/Symbolic/ExpandedProjectionOrigins.lean).
- [Minimum value origins](../../ExplainableCrypto/Helios/Symbolic/ExpandedValueOrigins.lean).
- [Partial equality and minimum closure](../../ExplainableCrypto/Helios/Symbolic/ExpandedPartialTransport.lean).
- [Eight SPOTs](../../ExplainableCrypto/Helios/Symbolic/ExpandedOriginSPOT.lean).
- [Executable gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedOriginExperiments.lean).

The controls retain a ciphertext-valued atomic handle refuting omission of the
handle premise, a constructed ciphertext with a public-name plaintext,
constructed and borrowed minimum partials, successful structured-key E5
returning a partial through a nonminimum wrapper, successful trustee E6,
nontrivial borrowed-slot equality transfer at the size-two base case,
nonconstant constructed equality in a diagonal election and the inability to
project a secret from a published partial.

The gate catches an atomic ciphertext's missing smaller plaintext and a
partial-as-pair defect at input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 each
pass 500 cases, size 40, `gaveUp=0`; 2048 deterministic inputs pass. It covers
both candidates and assignments, nonliteral honest values, zero through four
public ciphertext factors, constructed/borrowed partial values and successful
structured-key E5. Log: `tmp/variable-overlap/expanded-origin-gate.log`
(1014 jobs). Raw normalization is the bounded executable oracle; the general
claims use full E and the unchanged E5/E6 rules.

This closes additional origin and partial-value dependencies in the
[blueprint](helios-proof-blueprint.md), not the complete expanded-frame
static-equivalence theorem. Other value observations, the global smaller-test
and shared-minimum induction, historical process matching and the final
symbolic secrecy theorem remain open.

Full `lake build` passes **3637 jobs**, with **1907 nonempty standard-only
axiom reports**, **20 axiom-free reports**, **941 public theorem entries** and
**50 current-status documents**. Twenty-five new theorem audits include eight
SPOTs; one definition is checked. The generalized existing equality lemma and
its prior callers are included. Log: `tmp/variable-overlap/expanded-origin-full-build.log`.

Initial failures were proof engineering: implicit binders during Fin case
analysis, explicit handle-count arguments, unfolding frame/partial definitions,
and supplying concrete recipe arguments before publicness proofs. No protocol
equation, candidate claim or load-bearing premise was weakened.
