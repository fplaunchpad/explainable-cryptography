# Expanded public ciphertext minima and compression

Status: machine-checked, constructor minimum closure and conditional
constructed-only multiplication transport. Current milestone:
[B8](helios-proof-blueprint.md).
[`accepted_expanded_minimum_penc_of_children`](../../ExplainableCrypto/Helios/Symbolic/ExpandedConstructedMinima.lean)
proves that a public ciphertext constructor with source-minimum components is
globally minimum over the actual published handles. Its local shared-minimum
corollary needs no smaller-observation or smaller-minimum premise.

## Public constructor minimum size

The source theorem assumes public submissions and numeric source results;
accepted publication discharges the numeric premise. Valid ground candidates
and the original public-name policy remain explicit. Constructor keys, nonces
and payloads may use all expanded handles, including opaque trustee partials.

A globally minimum competitor has an exact ciphertext assembly. The existing
opaque nonce-factor theorem excludes an honest or mixed contribution when its
nonce equals an evaluated public recipe. This provenance argument works in
any opaque-protected frame whose policy protects the honest nonces. It needs
neither fresh distinct names nor a publicness premise for the supplied group.

The selected-key size plus group bound fits the original assembly size.
Minimum component costs then bound every public competitor and establish the
whole constructor's minimum size. This reuses existing group merge budgets,
full-E ciphertext inversion and opaque factor non-deducibility.

## Constructed-only multiplication

[`AssemblyCompressionTools`](../../ExplainableCrypto/Helios/Symbolic/AssemblyCompressionTools.lean)
proves the retained-handle syntax grammar, selected-key/group bound, publicness
of compression and strict compression of a nontrivial constructed-only tree.
Nonce and payload trees retain all occurrences; at least one repeated key
occurrence pays for the saving. A single constructor does not shrink.

[`ExpandedConstructedCompression`](../../ExplainableCrypto/Helios/Symbolic/ExpandedConstructedCompression.lean)
uses actual grouped interpretation for the compressed constructor. Existing
syntax key transfer supplies a destination ciphertext value for any public
assembly under smaller observations, including a nonminimum parent. Actual
ciphertext values derive key agreement; no new coherence predicate or premise
is introduced.

A source-minimum constructed-only assembly therefore has raw constructor
syntax. Combined with opaque nonce provenance, a minimum ciphertext with a
publicly denotable nonce also has raw constructor syntax. The origin theorem assumes the full supplied ciphertext equation; nonce
equality alone is not its premise.

`accepted_expanded_constructed_mul_shared_of_two_way_minima` closes the
constructed-only product branch under exactly the two smaller-minimum
hypotheses supplied by simultaneous induction. The existing bounded lifting
theorem supplies observations; public strict compression and its two-frame
value equations then reuse a smaller shared representative. Source parent
minimum size is unnecessary. The smaller-minimum hypotheses remain open in
the global proof.

## Controls and gate

The [gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedConstructedExperiments.lean)
detects incoherent-key compression, strict singleton compression and erased
duplicate public nonce occurrences at input zero, seed 1, zero shrinks. Seeds
1, 7 and 42 each pass 500 cases at size 40 with `gaveUp=0`; all 2048 deterministic
inputs pass. Fixtures have two through seven constructors in both swaps,
published-handle keys and components, delayed key aliases and repeated nonces.
Raw-normalized nonce/numeric summaries are bounded executable checks, not a
complete E decision procedure or a proof of minimum size.

Eight [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedConstructedSPOT.lean)
cover a four-node global constructor minimum with actual partial/result
components; opaque nonce provenance; exclusion of a cheaper honest alias;
the singleton boundary; repeated nonce compression from nine to six nodes;
the exact two-way constructed transport interface; wrong-key rejection; and
a four-node delayed key whose twelve-node product compresses to eleven nodes
before further minimization. The two-way induction control uses diagonal
candidates to inhabit its premises. Constructor and direct shared-compression
controls use actual different-vote frames.

The gate passes 1053 jobs. Generic tools, constructor minima and initial
compression pass 971 jobs; all eight controls and the public-nonce origin
addition pass 1094 jobs. Twenty-two public theorem audits cover this increment.
See the [results ledger](helios-results.md) for integrated evidence.

## Remaining frontier

Mixed ciphertext multiplication shared minima remain open,
along with remaining local constructor/selector and successful-case transport.
These must feed the global two-way shared-minimum induction. B8 final-frame
equivalence, B9 process matching and B10 full symbolic secrecy remain incomplete.
Coverage stays seven of ten milestones (70% unweighted, not effort remaining).


Integrated verification: full `lake build` passes 3721 jobs, including twenty-two
new theorem audits and all eight kernel controls. The log contains 2241 nonempty
reports using only `propext`, `Classical.choice` and `Quot.sound`, plus 21
axiom-free reports. The claim checker covers 1276 public theorem entries and
67 current-status documents. Log:
`tmp/variable-overlap/expanded-constructed-full-build.log`.

Honest-only combinations now have [global expanded-frame minima](helios-expanded-honest-minima.md)
and need no smaller premises for shared transport. Exact indexed occurrences
exclude honest groups from nonminimum ciphertext products with minimum children.

[Expanded mixed compression](helios-expanded-mixed-compression.md) now closes
mixed products with at least two public constructors under two-way smaller
minima. Minimum mixed competitors have exactly one constructor and preserve
honest indices, public nonce equality and zero-padded payload equality. The
remaining mixed case needs global padded payload minima with published numeric
handle costs.

[Expanded padded minima](helios-expanded-padded-minima.md) now close the general
one-constructor mixed case using published numeric-handle costs and shared
padded values. All multiplication local cases are assembled under the two
smaller-minimum hypotheses. Remaining pair/selector and successful-case
transport and the global simultaneous induction stay open.
