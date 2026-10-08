# Simultaneous minimum transport

Current status: [initial-frame static equivalence](helios-initial-static-equivalence.md)
is complete (B7). The [blueprint](helios-proof-blueprint.md) is at B8, final
transcript equivalence: twelve of twelve local operators and seven of ten
top-level milestones are closed. The evidence and remaining-work statements
below record this document's earlier checkpoint; their former B7 premises
are now discharged. Final-frame equivalence and the full secrecy theorem remain open.

Status: **machine-checked** bounded observation lifting and simultaneous
unbounded recipe induction; **machine-checked conditional** reduced
static-equivalence criterion. Constructed-only ciphertext products are now
discharged inside that induction. Subsequent [mixed compression](helios-mixed-compression.md) further restricts
remaining mixed products to exactly one public constructor. Successful decryption and proof checking remain.
The [blueprint](helios-proof-blueprint.md) stays at B7-M, with nine of twelve
operators and six of ten top-level milestones closed.

## Why the two bounds fit

[BoundedSharedMinima.lean](../../ExplainableCrypto/Helios/Symbolic/BoundedSharedMinima.lean)
defines `Frame.SharedMinimaBelow φ ψ N`: every public recipe whose node count
is strictly below N has a source-minimum representative preserving its value
in both frames. The bound applies to the original recipe. It does not assert
that comparing the recipe to its minimum also costs less than N.

`SharedMinimum.minimum_destination` transfers a source minimum using only
that recipe's reverse shared-minimum witness. The source least-size property
makes the original recipe no larger than the destination minimum witness, so
it is destination-minimum too.

`observationsBelow_of_shared_minima` derives every equality observation of
total size below N from both bounded transport directions and an explicit
both-minimum observation step. It inducts on total test size. Replacing both
recipes by shared minima either strictly lowers that total, or shows the
original recipes were already minimum. Reverse transport supplies destination
minimum status in the second case, and the observation step uses strictly
smaller tests. Every original recipe and minimum remains below N.

`observationsBelow_of_two_way_minima` supplies the already checked historical
minimum-observation assembly for fresh initial frames, valid ground vote
substitutions and either direction. There is no assumed full static equivalence.
`constructed_mul_shared_of_two_way_minima` applies this result to strict
[constructed compression](helios-constructed-compression.md), deriving
destination key coherence from the resulting observations.

## Unbounded induction and the remaining interface

[JointMinimumTransport.lean](../../ExplainableCrypto/Helios/Symbolic/JointMinimumTransport.lean)
defines `Frame.JointLocalMinimumTransport`: a local root with source-minimum
children may use strictly smaller shared minima in both directions.
`common_minima_of_joint_local` proves both full `CommonMinima` conclusions by
simultaneous strong induction on recipe size. It minimizes immediate children
in the chosen source frame, retaining both evaluated equalities. The rebuilt
parent is no larger than the original, so all strict local premises are
available from the same induction hypothesis. The conclusion covers arbitrary
unbounded recipes, including nonminimum parents.

[DecryptCheckMixedMulTransport.lean](../../ExplainableCrypto/Helios/Symbolic/DecryptCheckMixedMulTransport.lean)
classifies the remaining cases as successful `dec`, successful `checkspk`, or
`mul` with an exact coherent mixed ciphertext assembly. Non-ciphertext products
use shared partition reassembly; honest-only products are already minimum;
constructed-only products use strict compression and the derived bounded
observations. Previously closed operators retain their existing proofs.

The sufficient theorem established in this increment is
`Historical.General.staticEq_of_decrypt_check_mixed_mul_transport`.
Its two `DecryptCheckMixedMulTransport` premises still need proofs for the
actual compared initial frames. Each remaining local case may use both strict
smaller-minimum hypotheses. This is a proved induction principle with a reduced
case obligation, not a completed proof of initial-frame static equivalence.
The older broader criterion remains available as an earlier sufficient route.

## Controls and scope

[JointMinimumSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/JointMinimumSPOT.lean)
retains eight controls:

- A finite model refutes dropping reverse minima while the source transport
  and both-minimum step still hold.
- Equal-cost finite recipes refute dropping the observation step even when
  shared minima exist in both directions.
- A cutoff of two cannot justify an observation of total size three.
- Actual different-vote initial frames inhabit the bounded hypotheses at
  bound three; their atomic equality tests transfer and distinguish public names.
- The previous nine-versus-eight child-comparison counterexample persists.
- A coherent mixed product has twelve nodes and a nine-node public equivalent.
  It belongs to the remaining case. This fixture does not assert minimum
  immediate children, which remain a premise of local transport.
- The reduced static criterion is inhabited on the identical-vote diagonal
  and retains distinct public-name observations.
- The generic simultaneous theorem covers a strictly reducible wrapper.

The finite inference models are independent tests of the logical principle,
not historical protocol frames. The checked different-vote observation example
is bounded; the general induction theorem is unbounded but conditional on its
remaining local cases. These scopes must not be interchanged.

[JointMinimumExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/JointMinimumExperiments.lean)
detects all three known defects at input 0, seed 1, zero shrinks. Seeds 1, 7 and
42 each pass 500 configured cases at size 40 with gaveUp=0. The deterministic
backstop enumerates all 4096 combinations of four positive costs in `{1,2}`
and two binary value maps, at six bounds from zero through five. All 24576
instances pass the conditional inference check; **7872** satisfy its premises.
This is exhaustive only for that finite model. Log:
`tmp/variable-overlap/joint-minimum-gate.log`.

## Integrated verification

The main `lake build` succeeds with **3587 jobs**. Sixteen new public theorem
type/axiom checks include eight SPOTs; five definitions are checked. The log
contains **1665 nonempty standard-only axiom reports and 20 axiom-free reports**,
with no warnings, errors or `sorryAx`. The claim checker covers **699 public
theorem entries and 40 current-status documents**. Log:
`tmp/variable-overlap/joint-minimum-full-build.log`.

Targeted bounded-lifting, simultaneous-induction, reduced-interface and SPOT
builds also pass. Two intermediate failures were proof engineering: a copied
induction helper retained the old fixed destination on one side of equality,
and a wrapped tactic argument needed continuation indentation. Fixes restored
the intended statements; no conjecture, equation or assumption was weakened.

## Remaining work

The later mixed-compression result discharges groups with two or more public
constructors. Prove one-constructor mixed shared minima and successful
decryption/checking under the supplied simultaneous hypotheses. Then establish final public transcript
equivalence, historical process matching and the top-level symbolic secrecy
theorem. The [task list](../../task%20list.md) remains the sole development backlog.
