# Complete minimum-observation assembly

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked, conditional**. For the fresh initial historical
frames, static equivalence now reduces exactly to shared minimization in both
directions. Shared minimization remains unproved for those frames. Final
partial-decryption frames and process privacy are still separate open tasks.


The [local-root closure](helios-local-root-transport.md) now proves that minimum
children give minimum parents for constructed keys, partial constructors,
proofs and semantically stuck destructors. These roots are their own shared
representatives. The remaining transport interface requires new witnesses only
for nonminimum roots with minimum children: successful destructors, pairs,
ciphertext constructors and arithmetic. Those cases remain open in both swaps.


The [successful projection results](helios-projection-transport.md) now derive
exact honest proof-selector minima, including the one-candidate aggregate's
shorter component representative. Nonempty proof-only ballot suffixes are
minimum; the empty suffix uses bottom. Projections from explicit minimum pairs,
honest proof fields and proof-only/empty tails now have shared minima without
an observation premise. Ciphertext fields and tails retaining ciphertext fields
remain unresolved, alongside the other local root cases.

## Forward assembly

`Historical.General.minimum_equality_forward` takes fresh `Names n`, any two
valid ground candidate substitutions, two public recipes minimum in the source
world, and `ObservationsBelow` at their total syntax size. Any source equality
between those recipes then holds in the swapped world. The theorem does not
require a caller-supplied result head, normal representative, or destination
minimum judgment.

The proof normalizes one common source value and exhausts the ground syntax:

| Common normal value | Checked branch used |
|---|---|
| Name or constant | Literal atomic minima |
| Public key | Constructed/election-handle key comparison |
| fst or snd | Stuck projection comparison |
| Pair | Constructed pair or honest nonempty tuple tail |
| Partial-decryption constructor | Ordered component comparison |
| Decryption | Stuck decryption comparison |
| Multiplication | Normal non-ciphertext product partitions |
| Addition | Numeric contribution and semantic atom summary |
| Composition | Semantic factor bag |
| Ciphertext | Constructed/honest grouped ciphertext comparison |
| Proof check | Stuck-check comparison |
| Proof | Constructed/honest proof comparison |

Names and constants, and fst and snd, are separate syntax cases, giving fourteen
cases in total. A ground variable is impossible because its type is `Empty`.
Normality excludes reachable projection, decryption and proof-check matches
through the three new `Irreducible` exclusion lemmas. The multiplication case
uses the existing theorem that an irreducible product cannot have a ciphertext
E-value. Thus fusion and successful destructors are classified by their common
normal value, not by the original recipe's head.

## Reverse observations and the remaining obligation

`minimum_equality_swap_of_both_minima` applies the forward assembly in both
orientations. It explicitly requires minimum size in both worlds. Exchanging
the two candidate substitutions exchanges the actual frame definitions.

`minimum_observation_step_of_reverse_minima` supplies destination minima from
reverse `CommonMinima`, using the previous minimum-transport theorem. This
produces the complete minimum-pair iff step under that transport premise.
Combining it with forward shared minimization and the total-size induction gives
`staticEq_iff_common_minima`:

```text
StaticEq(source, destination)
  iff CommonMinima(source, destination)
      and CommonMinima(destination, source)
```

This equivalence retains freshness, the full restricted-name policy, every
positive candidate count and all valid ground candidate substitutions.
`CommonMinima` supplies one source-minimum public representative per public
recipe whose value agrees with that recipe in both worlds. Existence of a
minimum in each world separately does not establish this shared equality.

`staticEq_of_local_transport_both` reduces the remaining proof to local roots
with source-minimum children, in both orientations. Its conclusion is full
initial-frame static equivalence and its only extra transport premises are
the two `LocalMinimumTransport` obligations. The smaller-observation premise
is discharged internally by induction once those premises are available.

The generic criterion is now assembled for the historical frames. Proving
local shared minimization remains necessary before claiming initial-frame
privacy. A source-minimum root is its own shared representative by
`SharedMinimum.of_minimal`; the substantive cases are nonminimum roots with
minimum children. Preserve the earlier nine-versus-eight-node budget counterexample:
it still prevents an unproved child-minimization shortcut.

## Controls and executable evidence

Eight new kernel-checked controls cover:

- A successful projection changing its raw head, matching the gate's input-0
  counterexample.
- Concrete normal projection, decryption and proof-check exclusions.
- Delayed E5, E6 and proof-check matches refuting removal of normality.
- Equal values with multiplication and ciphertext raw heads under E7.
- Distinct permuted minimum products passed through the forward assembly on
  diagonal candidate assignments.
- A name/constant distinction passed through the bidirectional assembly on
  the actual different-vote worlds. Both recipes attain the one-node minimum;
  no observation has total size below two.
- A minimum honest handle with different raw values across the actual swap,
  whose self-equality transfers. This is one test, not static equivalence.
- A diagonal instance of the complete local-transport criterion that still
  distinguishes two public names.

The Plausible gate first rejects raw-head preservation at input 0, seed 1,
zero shrinks. Its positive property checks 22 independently derived literal
fixtures spanning all fourteen branch classes, including successful E5/E6,
proof checking, projection, and same-key ciphertext fusion. Seeds 1, 7 and 42
pass 500 configured cases each, size 40, `gaveUp=0`. The deterministic backstop
passes 2048 generated inputs, each checking all 22 fixtures. Name ranges vary
while preserving the fixture's required separations.

These experiments test raw normalization on their fixture family. They do not
decide arbitrary full-E equality or establish vote privacy. The unbounded
assembly theorem comes from kernel-checked case analysis and prior branch
proofs. Previous negative controls for missing shared transport remain relevant.

## Reproduce and audit

```sh
lake build
lake env lean ExplainableCrypto/Helios/Symbolic/ObservationAssemblyExperiments.lean
python3 scripts/check_helios_claims.py --build-log tmp/variable-overlap/observation-assembly-full-build.log
```

The new modules are `NormalDestructorExclusions`, `MinimumObservationAssembly`,
`ObservationAssemblyExperiments` and `ObservationAssemblySPOT`. The audit checks
sixteen new public theorem types and axiom sets, including the eight controls.
The full build passes (3533 jobs), with 1468 nonempty axiom sets using only
`propext`, `Classical.choice` and `Quot.sound`, and 17 axiom-free reports.
No warnings, errors or `sorryAx` occur. The claims checker covers 499 public
theorem entries and 27 current-status documents. Build evidence belongs in the [results ledger](helios-results.md#minimum-observation-branch-assembly-enquiry).

Trusted definitions remain E/E0, actual matching paths, irreducibility, public
recipes, minimum size, the general candidate frames and `StaticEq`. No new
cryptographic equation, public operation, custom axiom or confluence assumption
was introduced. See the [minimum-transport record](helios-minimum-transport.md)
and [static-equivalence record](helios-static-equivalence.md) for the surrounding
argument and the remaining scope.

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
