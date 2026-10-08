# Documented correction: ballot tuple termination

Status: source mismatch and counterexample machine-checked; correction authorised
by the user. This is a correction to our symbolic reproduction, not a claimed
published erratum or a concrete cryptographic repair.

## Printed definitions

In the [Cortier–Smyth author preprint](https://publications.bensmyth.com/2012-attacking-ballot-secrecy-in-Helios/),
§5.2.1, p. 24, tuples use the encoding

```text
(M1, ..., Mm) = pair(M1, pair(..., pair(Mm, ⊥)))
π_i(M) = fst(snd^(i-1)(M))
```

There are `m = 2ℓ + 1` ballot fields: ℓ ciphertexts, ℓ component proofs and
one aggregate proof. The repaired predicate on p. 27 includes
`π_(2ℓ+2)(ballot) =E ⊥`. These formulas were checked visually in the PDF,
as well as in the extracted text.

For a canonical tuple of m fields, that expression reduces to `fst(⊥)`,
not `⊥`. No equation E1–E9 or AC law supplies the missing equality.
This is proved by a separating algebra, rather than inferred from a failed
rewrite search. Conversely, adding an extra bottom-valued field followed by
an arbitrary tail satisfies the printed guard. It does not enforce the
claimed canonical tuple shape.

This observation is not a refutation of the full ballot-secrecy theorem.
It identifies a mismatch between the printed guard and canonical ballot
encoding. Figure 4 publishes the first two honest ballots without applying
this guard; a canonical ballot submitted at a subsequent checked position
would fail it. The existing finite attack model abstracts this tuple encoding
and did not purport to implement the literal guard.

## Adopted correction

The symbolic predicate now checks the remaining tail:

```text
snd^(2ℓ+1)(ballot) =E ⊥
```

This preserves the stated tuple representation and E unchanged. It changes
only the termination conjunct of the repaired ballot predicate; proof checks
and component-weeding checks remain explicit. The alternative of adding
`fst(⊥) = ⊥` would change E itself and is not adopted.

`Ballot.lean` defines `ProofValid`, `NoReuse`, `TailGuard` and `Accepted` for
any positive candidate count. Its parameter n represents ℓ = n+1 so that
aggregation needs no ciphertext identity absent from the source theory.
`PrintedGuard` remains available for comparison. A process semantics has not
yet been built around these predicates.

## Evidence

All declarations are in `ExplainableCrypto.Helios.Symbolic`.

| Claim | Declaration |
| --- | --- |
| Every canonical tuple fails the printed next-field guard | `canonical_tuple_fails_printed_guard` |
| This is an equational impossibility, not missing automation | `fst_bottom_not_bottom`, `EqE.denote` |
| Extra bottom plus arbitrary tail passes the printed guard | `extra_bottom_passes_printed_guard` |
| Every canonical tuple passes the corrected tail check | `canonical_tuple_passes_tail_guard` |
| A canonical one-candidate ballot has valid proofs | `oneCandidate_proofs_valid` |
| Corrected checks accept that ballot on an empty board | `oneCandidate_corrected_accepts` |
| Printed guard rejects that same ballot | `oneCandidate_printed_rejects` |
| Corrected acceptance still excludes replay onto a board containing the ballot | `accepted_excludes_replay` |

The acceptance control uses an empty board to isolate tuple/proof validity;
it is not a completed three-voter execution or a privacy proof. The finite
model's multi-voter controls remain separate. Reproduce these declarations via
`lake build ExplainableCrypto.Helios.Symbolic.Ballot` and the symbolic axiom audit.

Future claims must describe the target as the historical symbolic protocol
with this documented tuple-termination correction. The concrete `(1,1)` issue
remains a separate later obligation.

Validation: the full `lake build` passes (3277 jobs), including these controls
and their public-type/axiom audit. No claim of full symbolic ballot secrecy is
made by this correction.
