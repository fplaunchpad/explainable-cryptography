# Parametrized initial historical frames

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: constructors, protection, non-deducibility and honest-ballot validity
are machine-checked for
the two honest ballots and public key of Appendix B.2.1 and B.3. Candidate count
is n+1, ensuring all aggregate folds are nonempty. The definitions support both
swapped one-hot assignments and arbitrary name assignments. `Names.Fresh`
separately states distinct key/auxiliary names, injective voter/candidate nonce
names, and their separation from key/auxiliary names.

This document records the selected-index specialization. Appendix B also permits
honest abstention and arbitrary candidate-substitution representatives.
`AcceptedReconstructionSPOT.honest_abstention_scope_gap` proves that the
selected-index family omits an accepted all-zero ballot even up to E-equality.
The [general candidate frames](helios-candidate-substitutions.md) now fill that
gap: use `Historical.General.frame` for the full source model and subsequent
static-equivalence work. General constructor reconstruction completes source
Lemma 9 with the authorised tail guard. The old frame remains an exact
specialization, as checked by `General.selected_frame_specialization`.

## Source correspondence

| Source object | Lean definition | Representation |
| --- | --- | --- |
| Restricted nonce names | `Names.nonceNames` | Image of all two-voter/candidate pairs |
| Full restricted names | `Names.restricted` | Nonces, secret key and auxiliary name |
| Public key | `publicKey` | pk of the secret-key name |
| Candidate ciphertext | `ciphertext` | penc(key, nonce, selected bit) |
| Component proof | `componentProof` | spk(key, nonce, bit, ciphertext) |
| Aggregate proof | `aggregateProof` | spk over nonce composition, vote sum and ciphertext product |
| Ballot fields | `ballotFields` | All ciphertexts, then component proofs, then aggregate proof |
| Ballot | `ballot` | Existing bottom-terminated pair tuple |
| Swapped candidate assignment | `choice` | Exchanges the two selected indices, keeping names fixed |
| Initial frame | `frame` | Handles 0/1/2 expose zpk/y1/y2 |

All names above are in `ExplainableCrypto.Helios.Symbolic.Historical`.
`foldCandidates` starts with candidate zero and folds the remaining candidates;
it introduces no object-language identity. This definition preserves aggregate
expressions even before equational normalization.

## Checked scope

`ballot_fields_length` proves the exact 2(n+1)+1 field count;
`ballot_tail_guard` proves the documented corrected tail guard.
`frame_protected` proves the protection invariant for every handle, for any
protected-name set. Names appear only beneath pk/spk or as encryption randomness;
plaintexts are constants. Protection does not require `Names.Fresh`. The source's
freshness assumption is recorded explicitly and checked on the concrete fixture.

`frame_restricted_name_not_deducible` and `frame_secret_key_not_deducible` quantify
over recipes public with respect to the full restriction set.
`frame_nonce_composition_not_deducible` excludes arbitrary nonce remainders under
that policy. `frame_nonce_composition_of_nonce_public` instead requires only
`r.Public ns.nonceNames`, matching Lemma 9's explicit restriction. A recipe in
this latter theorem can mention key/auxiliary names when distinct from the
nonces. No secrecy of the key is claimed under the nonce-only policy.

These statements cover all positive candidate counts and both swapped worlds.
They prove no static equivalence between the worlds. The general honest-ballot
validity results below supply proof validity and scoped acceptance.
Accepted-adversarial-ballot characterization remains open, as do adaptive board extensions,
final partial-decryption frames and the process theorem.

## Controls and validation

The gate exercises counts 1–5, both swaps, independently counted selected bits,
field counts, handle mappings and ciphertext projections. Seeds 1, 7 and 42 pass
(500 configured cases, maximum size 40, `gaveUp=0`); all 256 deterministic inputs
pass. The missing-aggregate-field control fails at n=0, seed 1, zero shrinks.

Literal two-candidate controls retain five exact fields and all three aggregate
expressions, check freshness, verify the swapped assignments and exercise public
key/ciphertext handles. Both-world non-deducibility remains quantified over all
public recipes. The nonce-only policy control admits the literal key name and
still excludes composed nonces. The single-candidate boundary agrees with the
earlier accepted ballot and inherits its corrected acceptance theorem.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/HistoricalFrameExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3368 jobs pass, with 584 axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`. The final log has no warnings, errors or
`sorryAx`. The subsequent section records general ballot validity; the remaining
minimal-recipe obligations are tracked in the canonical task list.


## General honest-ballot validity

`HistoricalAggregation.lean` and `HistoricalValidity.lean` establish proof
validity and corrected acceptance for every positive candidate count and selected
candidate. All names below are in the `Historical` namespace.

| Claim | Declaration | Scope |
| --- | --- | --- |
| Homomorphic product equals aggregate encryption | `foldCandidates_ciphertexts` | Arbitrary component terms under one key; nonempty fold |
| One-hot vote sum equals one | `vote_sum_one` | E0 equality, with exactly one selected index |
| Honest ciphertext product encrypts one | `ciphertext_product` | Any positive candidate count |
| All tuple field offsets are correct | `ballot_project_ciphertext`, `ballot_project_proof`, `ballot_project_aggregate` | Actual ciphertext/proof/aggregate indices |
| Board aggregate equals constructor aggregate | `ballot_aggregate_ciphertext` | Product of projected ciphertext fields |
| All honest proof checks succeed | `honest_proofs_valid` | Component bit checks and aggregate check |
| Empty-board acceptance holds | `honest_empty_board_accepts` | Uses corrected `TailGuard` |
| Different fresh voters pass component weeding | `fresh_voters_no_reuse` | `Names.Fresh` and distinct voter indices |
| Second honest ballot is accepted after the first | `honest_accepts_after_other` | Same freshness and distinct-voter premises; one prior ballot |

The vote-sum proof uses exact optional numeric summaries and the count of a
selected index in `List.finRange`. It adds no global zero identity. Aggregate
proof checking synchronizes both the proof's vote sum and its bound ciphertext
with the encrypted aggregate. Component proof checks use E8/E9 according to the
selected bit. Weeding uses full-E ciphertext injectivity and fresh nonce-name
separation. Neither proof validity nor empty-board acceptance requires freshness;
the cross-voter acceptance theorem explicitly does.

The gate covers counts 1–5, every selected position and proof-field offsets.
Seeds 1, 7 and 42 pass (500 configured cases, maximum size 40, `gaveUp=0`),
as do 256 deterministic inputs. The false two-one collapse fails at n=0,
seed 1, zero shrinks. A full-E checked counterexample preserves this failure.
Controls check both two-candidate positions, both swapped second-voter cases,
first/last sum positions, and an exact aggregate encryption. Replay and a
colliding-nonce voter fixture are rejected.

Reproduce with `lake build`,
`lake env lean ExplainableCrypto/Helios/Symbolic/HistoricalValidityExperiments.lean`,
and `lake env lean ExplainableCrypto/Helios/Symbolic/Audit.lean`.
Validation: 3372 jobs pass with 603 axiom reports containing only `propext`,
`Classical.choice` and `Quot.sound`; no warnings, errors or `sorryAx` appear.
These theorems establish honest acceptance under the specified board conditions,
not the form of arbitrary accepted adversarial ballots or static equivalence.

## Minimum decryption of honest components

`HistoricalMinimalDecryption.lean` proves the decryption clause of the
minimum-recipe argument when the right recipe is full-E equal to any honest
ciphertext component in its actual swapped world. The recipe itself may have
arbitrary syntax. The three-handle substitution and nonce-only name policy are
explicit. Every positive candidate count, voter and component is covered.

An E5/E6 match would return the component's public zero/one plaintext; that
constant is a smaller equivalent recipe. Thus a minimum decrypt in this case
retains its head in every irreducible representative. The normal-form composition
theorem also shows E0 equality with dec applied to independently supplied normal
argument representatives. It retains all normality and E-value premises.

The control `DecryptionPathSPOT.historical_projected_decrypt_not_minimal` uses a
literal secret-key name permitted by the nonce-only policy. It successfully
decrypts an honest projected ciphertext to one and is nonminimum. This does not
claim that honest ciphertexts cannot be decrypted under that policy. Freshness
and secret-key nondeducibility are unnecessary for the smaller-constant argument.
The later [minimum-origin induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
now removes the right-argument value/certificate premise for every minimum
historical decrypt. The theorem in this section remains the earlier
honest-component interface.

Validation of the decryption-path increment: `lake build` passes (3383 jobs).
The audit reports 681 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. The final
log has no warnings, errors or `sorryAx`; every new public theorem type is printed
in `Symbolic/Audit.lean`.

## Ciphertext product leaves

`HistoricalCiphertextProducts.lean` proves that every initial handle exposes a
public key or whole ballot and is full-E distinct from every ciphertext. It
follows that any recipe for a ciphertext has at least two nodes, even when
literal names are unrestricted. This establishes the strict size bound needed
to use a public constant as a smaller plaintext recipe for honest components.

Both arbitrary component-equivalent recipes and the actual indexed field
projections now supply `CiphertextProduct` leaves, for any positive candidate
count, either voter and both swapped assignments. The product grammar combines
these leaves with constructed ciphertexts under one semantic key and preserves
repeated message/nonce occurrences. The historical minimum-decryption normal-form
theorem in that module retains a certificate premise and uses the nonce-only
policy. The later [minimum-origin induction](helios-minimal-recipes.md#minimum-historical-origins-and-destructor-composition)
derives the certificate for every minimum historical ciphertext recipe, under
any name policy, and proves exact constructor/honest-selector/product syntax.
Arbitrary nonminimum recipes are outside that claim.

Validation of the ciphertext-product increment: `lake build` passes (3387 jobs).
The audit reports 706 nonempty axiom sets, all subsets of `propext`,
`Classical.choice` and `Quot.sound`, plus 14 axiom-free declarations. The final
log contains no warnings, errors or `sorryAx`; new public theorem types are
printed by `Symbolic/Audit.lean`.
