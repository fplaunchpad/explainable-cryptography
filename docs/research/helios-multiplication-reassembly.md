# Shared multiplication reassembly

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. Shared minima of a source normal partition's pieces
reassemble into a shared globally minimum product. A well-founded size induction
discharges non-ciphertext products from the remaining static-equivalence
interface. Whole-ciphertext products and successful decryption/checking remain
unproved premises in both orientations.

## Reassemble the actual pieces

`MultiplicationPartition.pieces_ne_zero` excludes an empty partition of any
term. `Term.mul_factor_singleton_of_mem` proves that a representative of an
actual target factor has a singleton outer factor bag. Reassembly therefore
neither invents a multiplication unit nor treats an unflattened product as a
single target factor.

`reassemble_minimum_pieces` simultaneously constructs the old and new products
from a nonempty multiset of source recipe/target-value pairs. It keeps an exact
partition of each product, the same target endpoint, publicness, minimum size
of every new piece and destination equality of the two products. The old and
new raw costs may differ; each partition records its own exact cost.

`sharedMinimum_of_partition_shared_pieces` applies this construction to an
actual source normal partition. Exact old factor accounting makes regrouping
the original recipe E0-equal before substitution, preserving the destination.
The new partition has the original normal endpoint modulo E0 and minimum source
pieces, so `minimum_of_normal_partition` establishes global source minimality.
The destination is arbitrary under the same full initial-frame restriction;
no destination-minimum, freshness or observation premise is required here.

## Discharge non-ciphertext multiplication by size induction

`minimum_children_non_ciphertext_mul_shared` derives a normal source partition
from minimum children. Its endpoint is a product rather than a ciphertext.
At least two final pieces remain, and each piece is strictly smaller than the
original product. Shared minima of all strictly smaller public recipes therefore
suffice for reassembly. This theorem states that premise explicitly.

`Frame.common_minima_of_inductive_local` discharges such strict-size premises
by well-founded induction on raw recipe size. It first replaces the immediate
children by shared minima. Each replacement is no larger than its original
child, so a recipe strictly smaller than the replaced parent is also strictly
smaller than the original parent. This is a recipe-size argument, not the
previously refuted claim about fitting arbitrary comparisons into an observation
budget.

`inductive_local_of_decrypt_check_cipher_mul` combines this product case with
the previously checked constructors, projections, addition and stuck
destructors. `Frame.DecryptCheckCipherMulTransport` retains only successful
decryption, successful checking and products whose source value is one
ciphertext. The checked
`Historical.General.staticEq_of_decrypt_check_cipher_mul_transport` uses this
interface in both directions and retains explicit name freshness and valid
candidate substitutions. Neither different-vote remaining premise is asserted.

## Controls and evidence

Eight SPOTs retain four-to-one-node singleton reassembly, nine-to-three-node
duplicate reassembly, eleven-to-eight-node fused-group reassembly, the need for
both frame equalities, empty-partition impossibility, the discharged
non-ciphertext branch, a real nonminimum whole-ciphertext branch, and a diagonal
reduced-criterion instance with distinct public names. The first three controls
prove exact minimum witness sizes, excluding the unchanged nonminimum source
as a trivial witness.

The gate first detects source-only replacement and duplicate erasure at input
0, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 configured cases at size
40, gaveUp=0; all 2048 deterministic inputs pass. Inputs contain one through
seven pieces, repeated non-atomic recipes, wrappers and within-group ciphertext
fusion. Different fusion groups use distinct keys, matching the intended
normal-endpoint scope. Both honest assignments are checked.

The initial executable oracle failed at input 0 because raw normalization omits
E0 numeric collapse: it leaves zero-plus-one rather than literal one. The
corrected finite oracle compares ciphertext key syntax, nonce occurrence bags
and exact optional numeric summaries after raw normalization; other generated
factors retain their full raw syntax. This is not a full-E decision procedure.
The failed log is `tmp/variable-overlap/multiplication-reassembly-raw-oracle-failure.log`;
the passing log is `tmp/variable-overlap/multiplication-reassembly-gate.log`.

See the [results ledger](helios-results.md#multiplication-shared-piece-reassembly-result)
for integrated build/axiom evidence and the [blueprint](helios-proof-blueprint.md)
for the exact frontier. B7-M remains open until whole-ciphertext fusion minima
are shared for arbitrary minimum operands. The operator count remains nine of
twelve and the top-level milestone count six of ten.

The subsequent [joint transport result](helios-joint-minimum-transport.md)
discharges honest-only and constructed-only products in a simultaneous recipe
induction. The current reduced interface retains mixed honest/public products
and successful decryption/checking, with two-way smaller minima available.
