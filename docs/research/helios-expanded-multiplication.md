# Non-ciphertext multiplication equality in expanded frames

Status: machine-checked, conditional equality branch. Current milestone:
[B8](helios-proof-blueprint.md).
[`accepted_expanded_minimum_non_ciphertext_multiplication_equality_swap`](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulTransport.lean)
transfers equality between source-minimum multiplication-valued recipes that
are not ciphertext-valued. It derives normal partitions and strictly smaller
public comparison recipes in both expanded worlds.

## Public statement and scope

Assume fresh names, valid ground candidates, public submissions accepted in
sequence, arbitrary swap assignments, and source-minimum recipes `r` and `s`.
Each recipe has a multiplication E-value in the source frame, and neither has
a ciphertext E-value there. If the frames agree on public comparisons with
total syntax size strictly below `r.nodeCount+s.nodeCount`, then:

```text
EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s).
```

Source minimum size and the smaller-observation premise are load-bearing.
Destination minimum size is not assumed. Supplied multiplication values may
contain reducible factors and ciphertext fusion groups. The theorem derives
destination non-ciphertext status through the existing shape reflection result.

The non-ciphertext restriction is essential: two same-key ciphertext factors
can fuse to a single ciphertext, and a ciphertext constructor then has a
multiplication E-value without raw multiplication syntax. Ciphertext-valued
equality remains a separate open branch.

## Reused proof structure

[`MultiplicationOriginTools`](../../ExplainableCrypto/Helios/Symbolic/MultiplicationOriginTools.lean)
extracts the shared normal-product structural argument. The three original
initial-frame origin statements retain their types and use this helper. It
accepts explicit handle, projection-output and decryption-output exclusions;
it does not conceal a minimum or cross-frame premise.

[`ExpandedMulOrigins`](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulOrigins.lean)
excludes multiplication values for actual old key/ballot handles, trustee
partial slots and numeric result slots. A source-minimum normal-product value
therefore forces raw multiplication syntax. Destination origins use the
original recipe-size bound: a borrowed E6 success returns a numeric result,
which cannot have a multiplication value. This argument allows successful E6;
it does not assume decryption failure or spend a larger result-handle probe.
Successful minimum projections retain the existing pair/ciphertext/proof
classification, which excludes normal products.

[`ExpandedMulPartitions`](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulPartitions.lean)
uses those origins to show that each non-multiplication raw leaf normalizes to
a single factor in both worlds. It reuses `exists_normal_recipe_partition`
for normalization and actual ciphertext fusion, preserving all source factor
occurrences, publicness and recipe-size accounting. A non-ciphertext endpoint
has at least two factors, so every fused group has a strictly smaller public
recipe. Existing `MultiplicationPartition.transfer_normal_equality` transfers
the group comparisons and reassembles whole-recipe equality in both directions.

The increment introduces no new homomorphic law, arithmetic representation or
partition algebra. Numeric outputs, partial values, duplicate occurrences and
all public observations retain their existing model definitions.

## Controls and evidence

Nine [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulSPOT.lean)
cover all actual handle exclusions; global three-node minima for published
partial/result products; retained multiplicity and the absence of a zero-result
multiplicative unit; permuted published factors through the general equality
theorem; actual fusion within a surviving product; minimum representatives of
fused-product comparisons; nonminimum projection/E5 wrappers; successful
numeric E6; and a fused ciphertext with a product E-value and different raw head.
The equality controls use diagonal elections to inhabit the smaller-observation
premise. The public-factor minimum and multiplicity controls cover different
honest voters and both swaps.

The [gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedMulExperiments.lean)
detects all three mutations at input zero, seed 1, zero shrinks: preserving
unfused leaf counts, preserving hidden-product raw leaf counts, and retaining
a multiplication head after complete ciphertext fusion. Seeds 1, 7 and 42 each
pass 500 cases at size 40 with `gaveUp=0`. All 2048 deterministic inputs pass,
covering both candidates and swaps, one through five repeated partial factors,
result handles, same-key fusion and projection wrappers. These are finite
refutation checks, not a complete E-normalization or security decision procedure.

The gate passes 1046 jobs; expanded origins pass 943 jobs and the final equality
target passes 945 jobs. The shared helper and initial-origin refactor pass
860 jobs. Full `lake build` passes 3698 jobs, including all nine controls and
nineteen new theorem audits. The integrated log contains 2143 nonempty
standard-only axiom reports, 20 axiom-free reports, and coverage for 1177 public
theorem entries and 62 current-status documents. Log:
`tmp/variable-overlap/expanded-mul-full-build.log`. See the
[results ledger](helios-results.md).

## Remaining proof

[Grouped ciphertext comparison](helios-expanded-ciphertext-groups.md) now
classifies component equality using opaque public nonce protection and strict
group bounds. The [assembly theorem](helios-expanded-ciphertext-assemblies.md)
now closes the full conditional ciphertext-valued comparison.
[Non-ciphertext shared minima](helios-expanded-multiplication-minima.md) now
close that local multiplication transport case. Ciphertext-valued multiplication
shared minima, other local/successful cases and global induction remain open. B9 historical process matching and B10
full secrecy remain open. B8 is not complete, and this conditional branch does
not establish final-frame static equivalence by itself.
