# Constructed-only ciphertext compression

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked** strict compression and minimum-origin results;
**machine-checked conditional** shared transport. Blueprint position remains
[B7-M](helios-proof-blueprint.md), with nine of twelve operator cases and six
of ten top-level milestones closed. Constructed-only transport is not yet
unconditional in the standalone lemmas below. The subsequent
[joint induction](helios-joint-minimum-transport.md) discharges its smaller
premises within a reduced static criterion; mixed ciphertext groups remain open.

## Checked result and premises

[ConstructedCompression.lean](../../ExplainableCrypto/Helios/Symbolic/ConstructedCompression.lean)
reuses the existing ciphertext assembly, grouped semantics and homomorphic law.
It introduces no algebraic equations or cryptographic implementation.

`CiphertextAssembly.constructed_mul_compression_smaller` proves that a
multiplication-root assembly whose group is `.constructed r p` has strictly
greater raw node count than `penc t.keyRecipe r p`. Combining the two child
key/group budgets discards a repeated positive-cost key occurrence. All nonce
and message occurrences remain in the grouped syntax. Strict decrease does
not hold for singleton assemblies.

`constructed_compression_public` preserves any supplied public-name policy.
`constructed_compression_value` proves evaluated equality in an initial frame
under source coherence: the child encryption keys agree under full E equality.
The cost theorem alone does not establish this equality.

`minimum_constructed_group_recipe` excludes multiplication roots from minimum
coherent constructed-only assemblies. `minimum_ciphertext_public_nonce_form`
then proves that a minimum ciphertext with a nonce represented by a nonce-public
recipe has raw `penc` syntax. Existing nonce provenance excludes honest and mixed
groups. These theorems require neither a freshness nor an observation premise;
the minimum theorems use the stated full initial-frame restriction.

`constructed_mul_shared_of_coherent_both` obtains a shared source-minimum
representative from coherence in both initial assignments and shared minima
for all strictly smaller public recipes. Its companion
`constructed_mul_shared_of_smaller_observations` derives destination coherence
from `ObservationsBelow` at the original assembly's node count. **Both the
smaller-observation and smaller-shared-minimum premises remain explicit.**
The subsequent joint induction discharges them together within its local-to-global
criterion. Neither standalone theorem assumes or establishes full initial-frame
static equivalence.

## Controls and evidence

[ConstructedCompressionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/ConstructedCompressionSPOT.lean)
contains seven checked controls. A four-node key and a removable projection
wrapper produce an eighteen-node product. Grouping gives eleven nodes; the
existing zero-plus-one law gives an actual nine-node global minimum shared
across different vote assignments. Other controls retain singleton minimality,
refute wrong-key fusion to any ciphertext, refute source-only coherence in an
arbitrary destination, exclude honest contributions, classify every minimum
competitor of the fixture and inhabit the conditional interface on the diagonal.
The arbitrary-frame counterexample identifies a missing premise, not an attack
on the historical initial frames.

[ConstructedCompressionExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/ConstructedCompressionExperiments.lean)
first detects wrong-key fusion and false singleton strictness at input 0,
seed 1, with zero shrinks. Seeds 1, 7 and 42 each pass 500 configured cases at
size 40 with gaveUp=0. The 2048-input deterministic backstop covers two through
seven constructors, non-atomic and reducible keys and both assignments. The
executable comparison uses raw normalization, which omits E0 numeric collapse;
it does not decide all full-E equalities or prove global minimality.

The gate log is `tmp/variable-overlap/constructed-compression-gate.log`.
The integrated `lake build` succeeds with **3582 jobs**, fourteen new public
theorem type/axiom audits including seven controls, and two definition checks.
Log: `tmp/variable-overlap/constructed-compression-full-build.log`.
The claim checker covers **683 public theorem entries and 39 current-status
documents**. The full build has no warnings, errors or `sorryAx`; its theorem
axioms are limited to Lean's standard `propext`, `Classical.choice` and `Quot.sound`.

## Remaining work

The subsequent [joint transport result](helios-joint-minimum-transport.md)
resolves the smaller-premise induction for constructed-only products. Handle
mixed honest/public ciphertext groups next.
Successful decryption and proof checking, final transcript equivalence,
historical process matching and the top-level secrecy theorem remain open.
The [task list](../../task%20list.md) remains the only development backlog.
