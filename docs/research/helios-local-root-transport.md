# Local roots with minimum children

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked** for the minimum-parent closures below;
**conditional** for the reduced static-equivalence criterion. The unresolved
root cases remain necessary in both swap orientations. Initial-frame static
equivalence and full ballot secrecy remain open.


The [successful projection results](helios-projection-transport.md) now derive
exact honest proof-selector minima, including the one-candidate aggregate's
shorter component representative. Nonempty proof-only ballot suffixes are
minimum; the empty suffix uses bottom. Projections from explicit minimum pairs,
honest proof fields and proof-only/empty tails now have shared minima without
an observation premise. Ciphertext fields and tails retaining ciphertext fields
remain unresolved, alongside the other local root cases.

## Cases now closed

For every positive candidate count, both swaps and all valid ground candidate
substitutions, six minimum-parent lemmas prove:

| Parent | Additional premise beyond minimum children |
|---|---|
| Constructed public key | Full restricted-name policy |
| Partial-decryption constructor | Actual initial frame |
| Constructed proof | Public nonce child under the full policy |
| fst or snd | The evaluated child has no pair E-value |
| Decryption | No reachable E5/E6 match between evaluated children |
| Proof check | No reachable successful proof-check match |

The public theorems use the actual general initial frame and full name
restriction. They require neither freshness nor preserved observations.
Their children may evaluate to reducible terms. Minimum size concerns raw
public recipe syntax, not normality of substituted values.

Each proof chooses a minimum equivalent parent, applies the existing exact
origin theorem, and compares children using full-E injectivity. Minimum child
sizes give the original parent's size bound. Public key reconstruction cannot
use the election handle because the secret name is restricted. Constructed
proofs cannot borrow an honest component or aggregate nonce. The stuck
constructor cases retain semantic no-match premises; failed raw matching does
not suffice.

The six declarations in `MinimumParentClosure.lean` are
`minimum_pk_of_child`, `minimum_partial_of_children`,
`minimum_spk_of_children`, `minimum_stuck_projection_of_child`,
`minimum_stuck_decryption_of_children` and `minimum_stuck_check_of_children`.
Atoms and public handles already attain the one-node lower bound.

Every resulting minimum recipe is its own shared representative in any
destination with the same policy and handles. This fact does not assert that
its source and destination values are equal, or that it remains destination
minimum.

## Explicit remaining cases

`Frame.RootTransportCase` retains these possibilities:

- A projection whose evaluated child has a pair E-value.
- A decryption with an actual reachable E5/E6 match.
- A proof check with an actual reachable successful match.
- A pair, ciphertext constructor, multiplication, addition or composition.

`Frame.RemainingRootTransport φ ψ` requires a shared minimum only when the
public root has minimum source children, is itself **not** source-minimum,
and belongs to one of those cases. Thus minimum roots never require a new
witness through this interface.

`minimum_outside_root_cases` proves the case list complete for the actual
initial frame. `local_transport_of_remaining_roots` turns the remaining
obligation into `LocalMinimumTransport`. Finally,
`staticEq_of_remaining_root_transport` combines both orientations with the
[observation assembly](helios-observation-assembly.md) and establishes full
initial-frame static equivalence if both remaining-root premises hold.
Those two premises are unproved. The theorem retains freshness, valid
candidate substitutions and the full name restriction.

Pairs can be reconstructed from projections of published handles; arithmetic
and successful destructors can expose smaller representatives. Do not infer
closure of these cases from the six minimum-parent results. Preserve the
[child-comparison size counterexample](helios-minimum-transport.md#checked-obstacles-and-controls).

## Controls and evidence

Seven public SPOTs check:

- A partial constructor using two handles, its constructed public key, and a
  nested proof attain exact minima; the proof has ten nodes. Its source minimum
  is a shared representative in every destination frame.
- A projection of the election-key handle, a decryption with a named second
  argument, and a proof check with a named ciphertext argument instantiate the
  stuck-parent closures in both actual swaps.
- Weakening the historical policy to nonce names permits a minimum secret-name
  child whose pk parent has the shorter public election handle.
- An artificial frame publishing a partial decryption gives a shorter handle
  for the explicit constructor, despite literal minimum children. This is not
  a theorem about the historical final frame.
- A public reducible child gives a nonminimum constructed key when the child
  minimum premise is removed.
- Addition of zero to zero inhabits the remaining-root interface: both children
  are minimum, the parent is nonminimum, and literal zero is a shared minimum.
- The complete reduced criterion is inhabited on diagonal candidate assignments
  while preserving distinct public names. It does not prove different-vote
  transport.

The two bad gates detect shorter handles at input 0, seed 1, zero shrinks.
The positive finite probe uses seven root fixtures, 28 atomic/unary public
competitors, both actual historical swaps, and varying public name ranges.
Seeds 1, 7 and 42 pass 500 configured cases each, size 40, `gaveUp=0`; all 2048
backstop inputs pass. The competitor pool omits arbitrary larger syntax and
compares raw normal forms. These are bounded checks, not proofs of minimum size.
The unbounded minimum claims follow from the separate Lean theorems.

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/LocalRootExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/local-root-full-build.log
```

The four new modules are `MinimumParentClosure`, `RemainingRootTransport`,
`LocalRootExperiments` and `LocalRootSPOT`. The audit checks sixteen public
theorem types and axiom sets, including seven controls, and two definitions.
The full build passes (3537 jobs), with 1484 nonempty axiom reports using only
`propext`, `Classical.choice` and `Quot.sound`, and 17 axiom-free reports.
No warnings, errors or `sorryAx` occur. The claims checker covers 515 public
theorem entries and 28 current-status documents. Full build evidence is in the [results ledger](helios-results.md#local-minimum-root-closure-enquiry).

Trusted definitions remain E/E0, publicness, evaluation, minimum recipe size,
actual match predicates and initial frames. No cryptographic equation, public
operation, custom axiom or confluence assumption changed. Final published
partial decryptions, process matching, concrete cryptographic repair and later
backlog items remain required.

The subsequent [complete projection theorem](helios-complete-projections.md)
discharges every local fst/snd obligation with a minimum child. Exact honest
ciphertext-selector and all nonempty tail minima supply the remaining projection
representatives. The subsequent [pair transport result](helios-pair-transport.md) also
discharges pairing by exact honest-tail origins and honest-field/tail matches.
The [ciphertext constructor result](helios-ciphertext-constructor-minima.md)
also proves minimum-parent closure for penc. The reduced interface retains
successful decryption/checking and arithmetic. The
[composition minimum result](helios-composition-minima.md) also closes compose,
leaving successful decryption/checking, addition and multiplication in both
directions. Initial-frame
static equivalence, final partial-decryption frames and process privacy remain open.
