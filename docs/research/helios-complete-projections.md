# Complete local projection transport

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. Every fst/snd recipe with a source-minimum child
has a shared source-minimum representative in both initial historical frames.
The result covers every positive candidate count, valid ground candidate
substitutions, fresh names and the full name restriction. Initial-frame static
equivalence remains open because other local root cases remain unproved.

## Honest ciphertext selectors

`minimum_honest_ciphertext_origin` proves that a minimum public recipe equal
to honest ciphertext `(i,j)` is exactly the indexed selector
`(Term.var i.succ).project j.val`. Its premise uses full E equality, not raw
syntax equality. `minimum_ciphertext_selector` then proves that this selector
is minimum, with node count `j.val+2`.

The proof classifies the minimum recipe's ciphertext assembly and compares its
group with a single honest leaf. Protected nonce provenance excludes public
constructed and mixed groups. Equality of honest nonce bags forces a singleton
occurrence multiset. Both combination inversion and assembly inversion retain
multiplicity: neither a second honest occurrence nor a constructed contribution
can disappear. No zero unit or new cryptographic equation is introduced.

## All ballot tails and projections

`minimum_ballot_tail` proves minimum size `k+1` for every nonempty honest tail,
where `k < fieldCount n`. For a ciphertext prefix, the first ciphertext field's
minimum bounds the size of any equivalent explicit pair. Equality with another
honest tail fixes its position. The existing proof-suffix result covers the
remaining positions, including the one-candidate aggregate exception.

`ballot_tail_shared_minimum` includes the empty tail at `fieldCount n`.
Nonempty tails use themselves. The empty tail uses literal bottom, which has
size one; its indexed drop chain is not minimum.

`minimum_child_projection_shared` exhausts the local fst/snd cases:

- A child with no pair E-value gives a minimum stuck projection.
- An explicit minimum pair supplies its selected minimum child.
- A minimum honest tail supplies a ciphertext selector, component proof,
  canonical aggregate proof, or its next tail.

The one-candidate aggregate still uses its shorter component representative.
The theorem requires neither preservation of smaller equality tests nor
static equivalence. It retains source-child minimum size, freshness and the
actual initial-frame policy. It does not assert that every projection is itself
minimum or extend the result to frames publishing partial decryptions.

## Reduced static-equivalence obligation

`Frame.NonprojectionRootTransport` requires shared minima only for nonminimum
roots with minimum children in these cases: successful decryption, successful
proof checking, pairing, ciphertext construction, multiplication, addition and
composition. `remaining_transport_of_nonprojection` supplies all projection
cases to the earlier interface. `staticEq_of_nonprojection_transport` derives
initial-frame static equivalence if this reduced obligation holds in both
orientations. The subsequent [pair transport result](helios-pair-transport.md)
discharges pairing, and the
[ciphertext constructor result](helios-ciphertext-constructor-minima.md) closes
penc. The [composition minimum result](helios-composition-minima.md) closes
compose. Successful decryption/checking, addition and multiplication remain
unproved for different votes.

## Controls and evidence

Eight checked controls cover exact ciphertext minima and minimum origins;
nonce collisions giving a smaller public equal selector; occurrence multiplicity
and constructed contributions; every nonempty tail and the empty boundary;
both projections at every honest tail in the actual swapped frames; the
one-candidate aggregate exception; a real remaining arithmetic case; and a
diagonal instantiation of the reduced criterion retaining distinct public names.
The diagonal control is not a different-vote privacy theorem.

Before the general proof, the Plausible gate detects both deliberate defects
at input 0, seed 1, with zero shrinks: dropping freshness and treating occurrence
bags as sets. The positive campaign varies one through five candidate counts,
both voters, both swaps and mixed/repeated assemblies. It checks singleton
inversion, exact ciphertext values and indexed selector/tail node counts.
Seeds 1, 7 and 42 pass 500 configured cases each, size 40, `gaveUp=0`; all 2048
deterministic backstop inputs pass. These executable fixtures compare raw
normal forms and sizes; they do not decide full E equality or search all smaller
public recipes. The unbounded minimum statements come from Lean proofs.

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/CiphertextSelectorExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/complete-projection-full-build.log
```

The four new modules are `HonestCiphertextMinima`, `CompleteProjectionTransport`,
`CiphertextSelectorExperiments` and `CompleteProjectionSPOT`. The audit checks
18 public theorem types and axiom sets, including eight controls, and the two
new remaining-obligation definitions. The full build passes (3546 jobs), with
1519 nonempty standard-only axiom reports and 18 axiom-free reports. No warnings,
errors or sorryAx occur. The claims checker covers 551 public theorem entries
and 30 current-status documents. Build and axiom evidence is recorded in
the [results ledger](helios-results.md#ciphertext-selector-and-complete-projection-enquiry).

Trusted definitions remain E/E0, public recipes, actual fresh candidate frames,
tuple layout, ciphertext grouping, occurrence multisets, node count and shared
minimum representatives. The independent model checks use the source's E7
nonce multiplicity and the specified ballot layout. No additional claim about
a concrete implementation follows from these symbolic proofs.

Other root transport, final public partial-decryption frames, historical process
matching and full ballot secrecy remain open in the [task list](../../task%20list.md).
