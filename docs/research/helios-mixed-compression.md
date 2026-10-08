# Mixed ciphertext compression and minimum origins

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked** occurrence costs, coherent compression and minimum
origins; **machine-checked conditional** shared compression and reduced static
criterion. The [blueprint](helios-proof-blueprint.md) now locates B7-M at mixed
assemblies with exactly one public constructor. Multiple-constructor mixed
assemblies are discharged within the simultaneous induction. Nine of twelve
operators and six of ten top-level milestones remain closed.

## Exact cost and key agreement

[MixedCompressionCosts.lean](../../ExplainableCrypto/Helios/Symbolic/MixedCompressionCosts.lean)
defines `CiphertextAssembly.constructedCount`, counting public constructor
occurrences with multiplicity. Honest selectors contribute zero to this count;
their exact indexed recipe cost is retained separately.

For an assembly `t` grouped as `.mixed r p a`,
`mixed_compression_cost` proves

```text
nodeCount (mixedCombinationRecipe r p a) + t.constructedCount
  ≤ nodeCount t.recipe + 1.
```

The grouped recipe is one ciphertext constructed under the public-key handle,
multiplied by the exact honest selector combination. If the original tree has
at least two public constructor occurrences, the inequality is strict after
dropping the occurrence count. With exactly one constructor, grouping can have
the same size. The cost proof covers every group merge and preserves repeated
honest selectors and their candidate-index costs.

[MixedCompression.lean](../../ExplainableCrypto/Helios/Symbolic/MixedCompression.lean)
proves `key_agreement_public_key_of_nonconstructed`: any honest contribution
binds a coherent common encryption key to the actual public key.
`mixed_compression_value` then reuses grouped-value and mixed-combination
semantics to prove evaluated equality. Coherence remains explicit; the cost
inequality alone does not license replacing an unrelated key.

`minimum_mixed_constructedCount_eq_one` excludes two or more public constructor
occurrences from a source-minimum mixed assembly. `minimum_mixed_grouped_representative`
shows its grouped recipe has exactly the same global minimum size.
`minimum_mixed_combination_origin` classifies every minimum competitor of a
mixed value: it has one public constructor, the same honest index bag, an equal
public nonce and an equal **zero-padded** payload. Its grouped recipe has the
same cost. Freshness is used for the indexed nonce provenance comparison;
compression and its minimum occurrence count do not require freshness.

`minimum_mixed_of_minimum_nonce_atomic_payload` proves a global minimum theorem
for any minimum public nonce recipe and one-node public payload, with an
arbitrary nonempty honest combination. Every minimum competitor pays at least
the original nonce cost, one payload node and the same honest selector cost.
This result covers all positive candidate counts, both assignments and valid
ground vote representations, under the stated fresh-name/full-restriction
premises. It does not cover every minimum payload of larger size.

## Reduced unbounded route

`mixed_compression_shared_of_two_way_minima` uses the existing two-way smaller
shared-minimum hypotheses to derive bounded observations and transfer key
coherence. With at least two public constructors, strict compression gives a
smaller recipe to which the induction hypothesis applies.

[DecryptCheckSingleMixedTransport.lean](../../ExplainableCrypto/Helios/Symbolic/DecryptCheckSingleMixedTransport.lean)
reduces the previous mixed-product interface. The current sufficient theorem
is `Historical.General.staticEq_of_decrypt_check_single_mixed_transport`.
Its two `DecryptCheckSingleMixedTransport` premises retain successful `dec`,
successful `checkspk` and mixed products with exactly one public constructor.
Each case may use both strict smaller-minimum hypotheses. This restricts the
remaining proof obligation by a proved case split; it does not restrict the
attacker or bound recipe sizes in the final static-equivalence conclusion.

The one-constructor case remains substantial. A three-node payload `name + zero`
is minimum by itself, but its zero becomes redundant beside the honest numeric
message. A mixed parent with minimum immediate children can therefore shrink
from nine nodes to seven. The general remaining proof must minimize payloads
under zero-padded equality, preserving equality in both frames. It cannot infer
parent minimality from ordinary payload minimality.

## Controls and evidence

[MixedCompressionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/MixedCompressionSPOT.lean)
contains eight checked controls: a twenty-node repeated-index mixed tree with
a sixteen-node compression and fourteen-node shared global minimum; an already
minimum seven-node one-constructor term; exact higher-index occurrence costs;
failure of public-key binding without an honest contribution; the nine-to-seven
zero-padding example with minimum immediate children and remaining-case membership;
a removable nonce-wrapper counterexample; one-constructor classification of
every minimum competitor; and nonconstant diagonal inhabitation of the reduced
criterion. Different-vote shared representatives are checked independently of
the diagonal interface control.

[MixedCompressionExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/MixedCompressionExperiments.lean)
detects false singleton strictness and erased higher-index selector costs at
input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 configured cases,
size 40, gaveUp=0. All 2048 deterministic inputs pass, covering one through four
public constructors and one through four honest selectors, wrapped equivalent
keys and both assignments. Public occurrence counts come from an independent
leaf list. Value checks compare normalized keys, nonce occurrence bags and
numeric/atom message summaries; they are not a full-E decision procedure or a
global minimum search. Log: `tmp/variable-overlap/mixed-compression-gate.log`.

The [results ledger](helios-results.md) records integrated build and audit
evidence. The [task list](../../task%20list.md) remains the only development
backlog. One-constructor mixed shared minima, successful decryption/checking,
final public transcript equivalence, process matching and the full symbolic
secrecy theorem remain open.


Integrated verification: main `lake build` succeeds with **3592 jobs**.
Twenty-two new public theorem type/axiom audits include eight controls, with
four definition checks. The full log reports **1687 nonempty standard-only
axiom sets and 20 axiom-free reports**, without warnings, errors or `sorryAx`.
The claim checker covers **721 public theorem entries and 41 current-status
documents**. Log: `tmp/variable-overlap/mixed-compression-full-build.log`.

The [expanded mixed compression proof](helios-expanded-mixed-compression.md)
now extends occurrence bounds, common-key binding, strict shared compression
and minimum competitor origins to actual published handles. General padded
payload minima in that frame must account for published numeric costs.
