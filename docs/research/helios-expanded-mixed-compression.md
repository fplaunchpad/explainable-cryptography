# Mixed ciphertext compression after publication

Status: machine-checked, conditional shared transport for mixed assemblies with
at least two public constructors, plus minimum mixed origins. Current milestone:
[B8](helios-proof-blueprint.md). The general one-constructor case is now closed by the subsequent
[padded minimum result](helios-expanded-padded-minima.md).

## Preserve occurrences and the election key

[`MixedHandleTools`](../../ExplainableCrypto/Helios/Symbolic/MixedHandleTools.lean)
uses the existing constructor-occurrence counter, generalized to arbitrary
handle counts. Honest selectors count as zero constructed occurrences, even
though they evaluate to ciphertexts. Their indexed syntax costs remain exact;
repeated honest and public contributions are never discarded.

`mixedCombinationRecipeWith` constructs one ciphertext using the retained
election-key handle, then multiplies it by the existing honest combination
under the old-handle map. The occurrence bound gives its size plus the original
constructor count at most the original recipe size plus one. Two or more
constructors therefore guarantee strict compression. With one constructor,
the sizes can be equal.

The existing key-agreement theorem now supports arbitrary handle counts.
An honest contribution forces the common ciphertext key to equal the election
key. Constructed-only ciphertexts may still use unrelated public keys. The
expanded compression theorem derives key agreement from the actual ciphertext
value; callers need no separate coherence predicate.

## Close the multiple-constructor case

[`accepted_expanded_mixed_compression_shared_of_two_way_minima`](../../ExplainableCrypto/Helios/Symbolic/ExpandedMixedCompression.lean)
uses exactly the forward and reverse smaller-minimum hypotheses of simultaneous
induction. Existing bounded lifting supplies smaller observations, and existing
assembly key transfer supplies a destination ciphertext value. Compression
preserves both within-world recipe values. Its strictly smaller public syntax
then obtains a shared minimum from the induction hypothesis.

The theorem assumes fresh names, public accepted submissions, an actual source
ciphertext value, a mixed group and at least two constructed occurrences. It
does not assume the original parent is minimum. The global smaller-minimum
hypotheses remain to be discharged by the final simultaneous induction.

## Classify minimum mixed competitors

A minimum mixed assembly has exactly one constructor: two would contradict
strict public compression. Its grouped representative is itself globally
minimum and has exactly the original size.

[`expanded_minimum_mixed_combination_origin`](../../ExplainableCrypto/Helios/Symbolic/ExpandedMixedMinima.lean)
compares every minimum public competitor with a supplied public mixed
combination. Numeric result origins and opaque group equality recover a mixed
assembly with one constructor, the same honest index occurrence bag, an equal
public nonce and an equal zero-padded public payload. Its grouped recipe has
exactly the competitor's size. Fresh names, public submissions and numeric
source results remain explicit.

A minimum public nonce and a one-node public payload consequently give a
global minimum mixed combination. This includes actual partial/result handles.
The proof accounts for every public competitor's honest indexed cost, nonce
minimum and positive payload size. It does not settle general padded payload
minimum costs.

## Controls and gate

The [executable gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedMixedExperiments.lean)
detects three mutations at input zero, seed 1, zero shrinks: strict compression
with one constructor, deletion of an honest duplicate, and fusion of an actual
partial key with an honest election-key ciphertext. Seeds 1, 7 and 42 each
pass 500 cases at size 40 with `gaveUp=0`. All 2048 deterministic inputs pass
in both swaps. Trees have two through six public constructors and three through
seven honest selectors, published partial/result components and delayed key
aliases. Component summaries after raw normalization are an executable
refutation check, not a full E decision procedure or minimum-size proof.

Eight [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedMixedSPOT.lean)
cover a twelve-node product with an eleven-node grouped recipe and nine-node
global shared minimum; a seven-node minimum with one constructor and published
components; arbitrary minimum competitor origins and exact costs; the exact
two-way induction interface; honest duplicate retention; the necessity of an
honest contribution for election-key binding and direct rejection of the gate's
partial-key mutation; the remaining padded payload
problem with minimum immediate children; and equal-size regrouping of a minimum
whose constructor occurs on the right. The exact induction-interface control
uses diagonal candidates to inhabit its smaller-minimum premises. Direct
shared-compression controls use different votes.

The padded control has a globally minimum payload consisting of a public name
plus the published zero handle. Its mixed parent has minimum immediate children
but costs nine nodes; a seven-node shared minimum omits the payload's zero,
which becomes redundant beside the honest numeric message. The subsequent padded minimum theorem now handles this case without weakening
minimum-child transport.

## Remaining frontier

The subsequent [padded minimum result](helios-expanded-padded-minima.md)
closes the one-constructor mixed multiplication case using global zero-padded
payload minima that account for cheap published numeric handles. The initial frame's literal-only numeric cost formula cannot
be reused unchanged. Remaining local/selector and successful-case transport
must also feed the global two-way shared-minimum induction. B8, B9 and B10
remain incomplete; coverage stays seven of ten milestones (70% unweighted,
not effort or time remaining). See the [results ledger](helios-results.md)
for integrated verification.

Integrated verification: full `lake build` passes 3730 jobs, with twenty-one
new public theorem audits and all eight kernel controls, including direct
rejection of the partial-key mutation. The log contains 2280 nonempty reports
using only `propext`, `Classical.choice` and `Quot.sound`, plus 21 axiom-free
reports. The claim checker covers 1315 public theorem entries and 69
current-status documents. Log: `tmp/variable-overlap/expanded-mixed-full-build.log`.

[Expanded padded minima](helios-expanded-padded-minima.md) now close the general
one-constructor mixed case using published numeric-handle costs and shared
padded values. All multiplication local cases are assembled under the two
smaller-minimum hypotheses. Remaining pair/selector and successful-case
transport and the global simultaneous induction stay open.
