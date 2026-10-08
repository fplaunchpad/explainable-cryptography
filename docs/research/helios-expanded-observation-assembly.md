# Expanded minimum observations and final-frame lifting

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: machine-checked, conditional comparison assembly and exact transport
reduction. Current milestone: [B8](helios-proof-blueprint.md).
[`accepted_expanded_minimum_equality_forward`](../../ExplainableCrypto/Helios/Symbolic/ExpandedObservationAssembly.lean)
combines every expanded normal-value branch. It assumes source minimum recipes
and equality of strictly smaller public tests, then preserves their equality.
The caller supplies neither a normal form nor a value-class certificate.

## Exhaustive comparison assembly

The proof obtains a common normal ground value using the checked normal-form
existence theorem. It dispatches on that value's syntax, covering all twelve
operator heads plus names and constants. A ground variable is impossible.
Normality supplies failed destructor matching and excludes ciphertext values
from a normal multiplication head. Each case applies its existing expanded
comparison theorem, including actual partial and numeric result handles.

Fresh names, valid ground candidate substitutions, public submitted recipes
and sequential acceptance remain explicit. This reuses the existing E0–E6
model and all its branch proofs. It introduces no cryptographic equation or
new normalization algorithm.

`accepted_expanded_minimum_equality_swap_of_both_minima` combines forward and
reverse proofs into an iff when both recipes are minimum in both frames.
`accepted_sequence_reversed_candidates` derives reversed sequential acceptance
from initial-frame static equivalence. Neither acceptance nor destination
minimum size is silently carried across the swap.

## Exact remaining obligation

[`ExpandedMinimumLifting`](../../ExplainableCrypto/Helios/Symbolic/ExpandedMinimumLifting.lean)
proves that expanded-frame static equivalence is equivalent to shared minimum
representatives in both directions. A shared representative must be minimum
in its source frame and equal the original recipe in both frames. Reverse
transport supplies destination minimum size for the comparison step.

The same iff is proved for the actual final transcript and aggregate-partial
frame, using the existing exact public presentation equivalences. These
statements identify the remaining obligation; they do not prove it.

`accepted_expanded_observationsBelow_of_two_way_minima` supplies strictly smaller
public observations from shared minima below the same recipe-size bound in
both directions. It accepts arbitrary swap assignments and derives reversed
acceptance where needed. This is the interface for the remaining simultaneous
minimum-transport induction. Local transport in both directions also suffices
for expanded static equivalence with no residual observation premise.

## Refutation gate and controls

The initial gate failed at input zero: the actual candidate-one result has a
raw-normalized addition head but full-E value one. This refutes using raw
normalization as a complete E0 normal-form oracle. The failure is retained in
`tmp/variable-overlap/expanded-observation-falsifier.log` and a kernel control.
The gate now follows raw reduction with the existing top-level numeric summary
for zero/one aliases. This is an oracle for the stated fixtures, not a general
E decision procedure. The proof itself uses full normal-form existence.

The [corrected gate](../../ExplainableCrypto/Helios/Symbolic/ExpandedObservationExperiments.lean)
detects four defects at input zero, seed 1, zero shrinks: selecting the raw
published-result head, leaving a fused ciphertext in the product branch,
ignoring E6 binding, and treating raw normalization as complete for numeric
sums. Seeds 1, 7 and 42 each pass 500 cases at size 40 with `gaveUp=0`. All 2048
deterministic inputs pass, each with 21 fixtures in both assignments. They
cover all fourteen ground head classes, actual publication slots, E5/E6
success, projections and homomorphic fusion.

Ten [kernel controls](../../ExplainableCrypto/Helios/Symbolic/ExpandedObservationSPOT.lean)
cover the numeric-head counterexample, published-result head change, fused
product head change, full ciphertext binding, a distinct minimum result/literal
alias, cross-head distinction, reversal of two nonempty accepted submissions,
bounded lifting at arbitrary bounds, final/partial-frame lifting, and the need
for shared transport. The last reuses an explicitly finite size/equality
countermodel, not a Helios frame. The global lifting controls use diagonal
candidate assignments; they do not prove different-vote shared minima.

Targeted builds pass: gate 1051 jobs; complete comparison and lifting 968 jobs;
all ten controls 1089 jobs. Nineteen new public theorem audits cover this
increment. See the [results ledger](helios-results.md) for integrated evidence.

## Remaining work

Two-way shared minimum transport for arbitrary expanded public recipes remains
open. [Non-ciphertext multiplication](helios-expanded-multiplication-minima.md)
now closes its local transport case. [Constructed ciphertext minima](helios-expanded-constructed-minima.md)
close constructor and constructed-only product transport. Mixed
products, remaining selector/pair cases and successful-case transport must
still feed that induction. B8 final-frame equivalence, B9 historical
process matching and B10 full symbolic secrecy remain incomplete. The
blueprint remains at seven of ten milestones (70% unweighted coverage), not
an estimate of effort remaining.


Integrated verification: full `lake build` passes 3713 jobs, including nineteen
new theorem audits and all ten kernel controls. The log contains 2203 nonempty
reports using only `propext`, `Classical.choice` and `Quot.sound`, plus 20
axiom-free reports. The claim checker covers 1237 public theorem entries and
65 current-status documents. Log:
`tmp/variable-overlap/expanded-observation-full-build.log`.

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

[Expanded pair/selector transport](helios-expanded-pair-selector-minima.md) now
closes those three local roots without smaller-test premises. All local roots
and the simultaneous induction are assembled conditionally: successful
decryption/checking transport in both directions is the remaining requirement
for expanded, partial and final static equivalence.

[Expanded successful-check transport](helios-expanded-successful-checks.md) now
closes `checkspk`, retaining whole-ciphertext binding and exact honest combination
origins. The remaining local interface for all three frame presentations is
successful decryption in both directions; B8 local coverage is now 11/12.

[Expanded public decryption](helios-expanded-public-decryption.md) now closes
direct E5 and constructed-partial E6. The remaining local case is complete
borrowed trustee tally-binding transfer for minimum ciphertexts. B7 handles
retained old recipes; general nested new-handle binding remains unproved.

[Result-handle realization](helios-result-handle-binding.md) now transfers full
tally bindings for all public old-plus-results recipes, including nested uses,
without size or minimum hypotheses. Only minimum ciphertexts without a
result-only presentation remain in the trustee-binding callback. A checked
ten-node minimum result-nonce recipe refutes old-only syntax and grows to
fourteen nodes under numeral realization.
