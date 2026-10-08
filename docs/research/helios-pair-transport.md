# Shared minima for constructed pairs

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked**. A pair of source-minimum children has a shared
source-minimum representative across the initial swapped frames. Fresh names,
the full name restriction and valid ground candidate substitutions remain
explicit. Every positive candidate count is covered. Full static equivalence
remains open. The subsequent
[ciphertext constructor result](helios-ciphertext-constructor-minima.md)
discharges penc, and the [composition minimum result](helios-composition-minima.md)
closes compose. Successful decryption/checking, addition and multiplication
remain unproved.

## Matching honest fields

`minimum_component_match_transfer` and `minimum_aggregate_match_transfer`
preserve a minimum recipe's equality to the specified honest proof field in
any destination assignment. Minimum proof origins exclude public construction
of a protected honest nonce. Fresh component and aggregate nonce provenance
identifies the matching field. The one-candidate component/aggregate alias
survives in both worlds.

`minimum_honest_field_match_transfer` covers every field position. Ciphertext
matches use the exact minimum selector origin from the
[complete projection result](helios-complete-projections.md). Proof matches use
the two theorems above. No smaller-observation hypothesis is required. The
indexed target selector need not be minimum; this matters for the one-candidate
aggregate.

`honest_field_public_size_bound` gives a uniform lower bound of `k+1` nodes for
any public recipe matching field `k`. It does not require that recipe to be
minimum. The sharper selector bound `k+2` applies to ciphertext and component
fields, and aggregate fields at larger candidate counts. At one candidate,
field 2 has a three-node component representative, so the uniform bound is
sharp.

## Exact minimum tail origins

`minimum_honest_tail_origin` proves that any minimum recipe equal to nonempty
tail `(i,k)` is literally `(Term.var i.succ).drop k`. A constructed pair cannot
be such a minimum: its first child costs at least `k+1`, and the other child
and pair node make the whole recipe strictly larger than the `k+1`-node tail.
An honest-tail competitor has the same voter and position by fresh tail
identity.

`minimum_honest_tail_match_transfer` also covers the empty tail. Nonempty
matches transfer by exact syntax. At the empty boundary, minimum constant
origin forces literal bottom. The empty indexed chain is not claimed minimum
or uniquely associated with a voter.

## Pair transport and remaining work

`minimum_children_pair_shared` chooses a minimum equivalent of the constructed
pair and classifies its origin. If that equivalent is another explicit pair,
component injectivity and child minimum size show that the original pair is
already minimum. The original recipe is then its own shared representative.

If the equivalent is an honest tail, equality of pairs gives a match between
the first child and the honest field, and between the second child and the
remaining tail. The field and tail matching theorems preserve both matches in
the destination. Reconstruction uses the tail's actual pair value, so the same
honest tail is a minimum equivalent in both worlds.

`Frame.CryptoArithmeticRootTransport` retains only successful decryption,
successful proof checking, ciphertext construction, multiplication, addition
and composition, for nonminimum roots with minimum children.
`nonprojection_transport_of_crypto_arithmetic` supplies pairing to the previous
interface; the earlier theorem already supplies projection.
`staticEq_of_crypto_arithmetic_transport` derives initial-frame static
equivalence if these remaining obligations hold in both orientations. Neither
premise is asserted for different votes. Ciphertext construction is discharged
by the subsequent constructor result, and composition by the later minimum
closure. Successful decryption/checking, addition and multiplication remain open.

## Controls and reproducible evidence

Seven public SPOTs retain:

- A five-node reconstruction with minimum children but a shorter, one-node
  honest ballot handle, equal in both actual swapped frames.
- Exact nonempty-tail origin, with literal bottom refuting the same claim at
  the empty boundary.
- The last one-candidate tail reconstructed from its shorter component proof
  and bottom, including a shared minimum and strict reduction in size.
- The sharp three-node bound for one-candidate field 2, refuting a uniform
  four-node lower bound.
- Literal public pair transport, distinct ordered fields, and failure of
  unconditional pair eta on a public name.
- Colliding nonces making a different one-node minimum ballot handle equal,
  directly refuting exact tail origin without freshness.
- A diagonal instantiation of the reduced static-equivalence criterion with
  distinct public names. This is not a different-vote privacy theorem.

The pre-proof Plausible gate detects the two deliberate defects at input 0,
seed 1, with zero shrinks: minimum children forcing a minimum pair, and pair
eta on arbitrary values. Positive checks reconstruct every nonempty tail from
its canonical first field and remainder, retain the one-candidate alias and
empty boundary, compare indexed sizes, and reject reversed fields. Seeds 1,
7 and 42 pass 500 configured cases each, size 40, `gaveUp=0`. All 2048
backstop inputs pass over one through five candidates and both swaps.
These raw-normal-form fixtures do not decide arbitrary E equality or prove
minimum size; the general Lean origin and size proofs establish those claims.

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/PairTransportExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/pair-transport-full-build.log
```

The five new modules are `HonestFieldTransport`, `HonestTailOrigins`,
`PairMinimumTransport`, `PairTransportExperiments` and `PairTransportSPOT`.
The audit checks 16 public theorem types and axiom sets, including seven
controls, plus two remaining-obligation definitions. The full build passes
(3551 jobs), with 1535 nonempty axiom reports using only propext, Classical.choice
and Quot.sound, and 18 axiom-free reports. No warnings, errors or sorryAx occur.
The claims checker covers 567 public theorem entries and 31 current-status
documents. Build and axiom evidence is in the [results ledger](helios-results.md#pair-constructor-transport-enquiry).

Trusted definitions remain EqE/E0, full public-recipe policy, actual candidate
frames, tuple layout, nonce provenance, minimum node count and SharedMinimum.
The independent semantic reference is the specified tuple layout and projection
equations. No global pair eta rule, new cryptographic equation, public operation
or custom axiom is added. Final public partial-decryption frames, historical
process matching and full ballot secrecy remain open in the
[task list](../../task%20list.md).
