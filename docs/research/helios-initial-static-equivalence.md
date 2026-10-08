# Initial honest-frame static equivalence

Status: **machine-checked**. B7, the initial-frame obligation corresponding to
source Lemma 10, is complete in the encoded symbolic model. The maintained
[blueprint](helios-proof-blueprint.md) moves to B8: accepted adversarial ballots
and final transcript equivalence. The full symbolic secrecy theorem remains
unproved until final observations and historical process behavior are covered.

## Public theorem

In namespace `ExplainableCrypto.Helios.Symbolic.Historical.General`:

```lean
theorem initial_frame_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right)
```

This covers every positive candidate count (`n + 1`), fresh names, valid ground
candidate representations, abstention and both assignments of the two honest
voters. `Frame.StaticEq` quantifies over **every pair of public recipes**, with
no size bound, and compares equality modulo the full E theory after evaluation.
The policy is `ns.restricted`, including the election secret and honest nonces.
No observation, common-minimum, successful-destructor or confluence premise
remains in this theorem. Candidate validity is a field of the supplied
`CandidateSubstitution` structures, not an omitted assumption.

The trusted semantics are the documented symbolic terms, E1–E9/E0 equations,
public-name restrictions and historical initial frame with key handle 0 and
two ballot handles. This result does not establish computational cryptographic
security, concrete implementation correctness or final-frame equivalence.

## Final decryption obligation

[SuccessfulDecryptionClosure.lean](../../ExplainableCrypto/Helios/Symbolic/SuccessfulDecryptionClosure.lean)
discharges the final local operator in five public theorems.

`minimum_successful_decryption_ciphertext_form` shows that successful
decryption with minimum children must consume a raw public `penc` constructor.
Minimum ciphertext grouping supplies either a constructed, honest or mixed
assembly. An honest or mixed group binds its key to the election public key.
Direct E5 success would then deduce the restricted election secret. For E6,
the minimum partial-key origin exposes an explicit public argument deducing
the same secret. Non-deducibility excludes both. A minimum constructed-only
assembly is already a raw `penc`: otherwise compression strictly shortens it.

`minimum_key_constructed_decryption_transfer` transfers success and returns
the explicit plaintext recipe. E5 uses the smaller comparison between the
ciphertext key and `pk` of the supplied secret. E6 uses the minimum partial-key
syntax and smaller key/binding comparisons. The unsorted model also permits
a partial-decryption term itself as an E5 secret key; that alternative is
retained. The E6 comparison binds the complete supplied ciphertext.

`minimum_children_decryption_shared_of_two_way_minima` covers successful and
stuck cases. In the successful case, the plaintext is an actual minimum child
of the minimum ciphertext. Its recipe is the shared witness, with its own
evaluated value in each world; the proof does not assume those two ground
values are identical. Stuck decryptions use the established minimum theorem.

`successful_decryption_transport` supplies both remaining instances of the
simultaneous induction interface. `initial_frame_staticEq` applies the
previously checked lifting theorem. All twelve local operators are therefore
closed, including the earlier [successful checking result](helios-successful-checks.md).

## Controls and gate

[SuccessfulDecryptionSPOT.lean](../../ExplainableCrypto/Helios/Symbolic/SuccessfulDecryptionSPOT.lean)
contains eight checked controls:

- An eleven-node E5 decrypt uses a three-node partial-decryption term as its
  secret and returns the public ballot handle. Its children are actual minima.
- A nineteen-node E6 decrypt binds the complete seven-node ciphertext and
  enters the full local operator theorem with minimum children.
- The general initial theorem applies to different, nonliteral candidate
  worlds; their ballot values are syntactically different and distinct public
  names remain unequal modulo E.
- One candidate retains abstention, a selected vote and component/aggregate
  proof aliasing under unbounded static equivalence.
- Exposing the election secret produces an actual distinguisher: the same
  public recipe returns zero before the swap and one afterwards. That recipe
  is excluded by the full policy. This refutes removing the secret restriction.
- A removable ciphertext wrapper still decrypts but is neither minimum nor
  a raw `penc`, retaining the minimum premise of the syntax classification.
- Changing a published E6 binding blocks the match and is detected by a
  strictly smaller public equality comparison.
- A wrong literal secret cannot decrypt the name-90 ciphertext.

[SuccessfulDecryptionExperiments.lean](../../ExplainableCrypto/Helios/Symbolic/SuccessfulDecryptionExperiments.lean)
first detects the existing omit-E5 and omit-binding mutations at input 0,
seed 1, zero shrinks. The positive campaign passes seeds 1, 7 and 42, 500
cases per seed, size 40 and `gaveUp=0`; 2048 deterministic inputs also pass.
The generated scope includes both rules, nested public keys, nonconstant
payloads, smaller probes and both candidate assignments. Raw normalization is
used only on these generated cases; failure of arbitrary raw normalization
is not treated as failed E equality. Gate log:
`tmp/variable-overlap/successful-decryption-gate.log` (992 jobs).

## Remaining work

Integrated evidence: full `lake build` passes **3607 jobs**. The audit covers
**779 public theorem entries** and **44 current-status documents**, with
**1745 nonempty standard-only axiom reports** and **20 axiom-free reports**.
The increment adds thirteen public theorem audits, including the eight SPOTs.
`initial_frame_staticEq` depends only on the standard Lean axioms `propext`,
`Classical.choice` and `Quot.sound`. Log:
`tmp/variable-overlap/initial-static-equivalence-full-build.log`.

B8 must instantiate shared accepted-ballot reconstruction using the initial
theorem, derive the tally/transcript arguments and prove static equivalence of
the actual final frames including public partial decryptions. B9 requires the
historical process transitions and matching proof. B10 assembles the full
labelled-bisimilarity and symbolic secrecy theorem. Equal tallies alone do not
discharge any omitted public observations.

The blueprint records seven of ten top-level milestones, or **70% unweighted
milestone coverage**, and twelve of twelve local operator cases. These counts
do not measure effort remaining or establish that the full proof is 70% of the
way through its difficulty.
