# Helios symbolic and computational scope comparison

The completed symbolic theorem and the revised computational secrecy result
concern different repaired election models. This is a declaration-backed model
audit, not a proved correspondence or a computational-soundness theorem. The
historical symbolic B1–B10 endpoint is unchanged. The computational milestone is
**3/3 complete under the revised boundary**: Lean proves the encoded-attacker
coverage and conditional secrecy implication, while the stated uniform-PPT
coverage and reduction-efficiency justification remain external mathematics.
The publication package is complete for this increment. TM cleanup is outside
its scope.

The development has three distinct layers. The initial finite-handle experiment
in [Model.lean](../../ExplainableCrypto/Helios/Model.lean), `Replay.lean` and
`Permutation.lean` supplies attack witnesses and controls. The historical source
theorem uses the unbounded symbolic term language and finite scoped processes.
The computational theorem uses actual field/group transcripts and the fixed
`ElectionOracle` game. The first layer is not the scope of the completed
symbolic theorem.

## Classification

**Aligned** means the inspected definitions share the stated feature; it does
not assert a proved cross-model relation. **Reconcile** identifies a scope,
representation or observation choice that a future common specification must
make explicitly. **Potential obstruction** identifies a concrete semantic
mismatch that prevents treating the present models as identical; it is not an
impossibility theorem for every possible abstraction or refinement.

| Dimension | Historical symbolic endpoint | Computational endpoint | Assessment |
| --- | --- | --- | --- |
| Election shape | `Names n` and `CandidateSubstitution n Empty` give `n+1` candidates; `scopedVoterElection` has two honest voters and arbitrary finite `extra` administration inputs. | `PublicParameters` is populated with candidates `[0,1]` and voters `[0,1,2]`; `ElectionOracle.world` makes two honest attempts and one attacker submission. | **Reconcile.** The symbolic theorem is parameterized by election size. The computational result is the fixed two-candidate, three-voter instance. Generic ballot algebra does not enlarge the final game. [S1, S2, C1, C2] |
| Honest choice and abstention | Arbitrary valid ground candidate substitutions have at-most-one bit values, including abstention. Two such choices are swapped. | `strongHonestBallot` encrypts `(voteScalar vote,0)`; the two honest voters receive `vote` and `!vote`. Thus the game swaps a first-candidate vote and abstention. | **Aligned** on at-most-one validity and equal honest totals; **reconcile** the different challenge families. The initial finite X/Y attack experiment is another fixture. [S3, C3] |
| Ballot and repair | `ProofValid` checks component and aggregate symbolic proofs; `TailGuard` is the documented tuple-termination correction; `NoReuse` checks components across all earlier candidate positions. | `Ballot.StrongValid` binds generator, public key and ciphertext into the proof hash. `ExpandedFreshFor` also compares implicit aggregates against components and aggregates. Key/decryption hashes bind their statements. | **Potential obstruction.** These are different predicates. The concrete repair is stronger than component weeding and includes a concrete hash-binding requirement absent from the symbolic proof syntax. The tuple-tail correction is not silently turned into a concrete identity exclusion. [S4, C3, C4] |
| Cryptographic operations | `Term`, `Equation` and `EqE` give the explicit historical signature and E1–E9/AC congruence. Encryption/proof arguments have no public projection destructor. Nonempty products add no group-identity or inverse laws. | `encryptWith`, `Proof01`, and scalar/group arithmetic expose complete commitments, challenges and responses. The identity exists, nonce sums can be zero, and `neutralProof` and proof-response rerandomization are actual operations. | **Potential obstruction.** A cryptographic implementation admits operations and equalities beyond the historical theory. Symbolic secrecy does not rule out these concrete attacks. [S5, C5] |
| Attackers | Arbitrary public recipes and actual source free/bound actions, with public-domain and private-name policies; no polynomial recipe-size restriction. The process scope is finite and uses static channels. | Stateful preparation, `castBallot` and `guessVote` are arbitrary typed oracle computations. `ElectionSecurityFamily.Family` bounds their queries and private output sizes polynomially in actual encoded inputs, with all typed reply branches covered. | **Reconcile.** Neither class is simply the other: symbolic attackers are unbounded within a restricted operation language; computational attackers have richer arithmetic under an efficiency policy. Uniform PPT implementations satisfying that resource interface are justified externally. [S1, S6, C2, C6] |
| Trustees and trust | `trusteeAgent` contains one honest secret and a private tally/partial exchange. It publishes the aggregate partial tuple and result tuple through the board. | The final game samples one honest secret and publishes its key proof, aggregate decryption shares and their proofs. | **Aligned** on the displayed single-honest-trustee trust setting; **reconcile** proof messages and secret/private-channel representations. Neither endpoint proves adaptive corrupt-trustee security, threshold setup, or a network authentication implementation. [S7, C1, C2, C4] |
| Board and eligibility | Two honest private-channel inputs are publicly relayed in order. Later scheduled public inputs are checked sequentially against all earlier accepted ballots. | `repairedSubmitOracle` verifies the full ballot before expanded freshness; accepted identified ballots are appended. The three scheduled identities implement eligibility. | **Aligned** on an honest board and sequential acceptance; **reconcile** the validation predicates and the absence of parameterized later voters in the computational game. There is one election, no revoting, and no modeled coercion schedule. [S7, C7] |
| Rejection | `collectBallots` selects `.nil` on guard failure. Rejection has no later tally/partial/result publication. | `repairedSubmitOracle` returns an explicit invalid-proof or reused-ciphertext decision and the unchanged board. `finishWithCoins` continues to the full result and tally. | **Potential obstruction.** Stop-on-rejection and retained-board publication are different observable behaviors. A bridge must choose or relate them, not erase the difference by citing equal successful tallies. [S7, C2, C7] |
| Public observation schedule | Initial key handle; first and second honest-ballot outputs; after all scheduled successes, a partial tuple and a result tuple. `boardFinish` adds neither a public tally-ciphertext output nor an attacker-ballot relay. Full frame equality tests remain available after each actual output. | The cast callback receives `PublicPrefix`; guessing receives `PublicResult`, including prefix, submitted ballot, decision, accepted board, encrypted tally, decryption shares/proofs and optional decoded tally. The fingerprint and setup/key proof are explicit. | **Potential obstruction** to direct equality of public traces; **reconcile** whether additional concrete fields are derivable, simulatable or additional leakage under a proposed common interface. No such cross-model result is claimed here. [S7, S8, C1, C2] |
| Tally and decoding | Nonempty homomorphic products, symbolic partial decryption and E6 yield bounded numeral results on accepted elections. | `boardTally` sums retained ciphertexts, then publishes group shares and `decodeBounded`, which searches through the board length and returns `Option Nat`. It also handles retained-board rejection. | **Aligned** on candidatewise homomorphic aggregation; **reconcile** numeral interpretation, decoding failure and rejected runs. The checked public bounds derive board lengths ≤2/3 and every successful final decoded value ≤3. [S8, S9, C1, C8] |
| Randomness and collisions | Fresh restricted names satisfy `Names.Fresh`, candidate/nonce freshness and channel freshness. This is not a probabilistic sampling assertion. | Honest historical nonzero sampling retains collisions; aggregate nonce zero remains possible. The secrecy proof uses statistical simulation bounds, replay/extraction and fair-bit replacement with explicit negligible errors. | **Reconcile.** Fresh symbolic atoms need a probabilistic interpretation and collision accounting. They are not automatically independent sampled nonzero field elements. [S1, S2, C5, C9] |
| Secrecy statement | `scopedVoterElection_ballot_secrecy` proves source weak labelled bisimilarity, including full-frame static equivalence and matching internal/free/bound actions. | `ElectionSecurityFamily.Family.ballot_secrecy` proves negligible guessing bias for the original resource-bounded attacker, assuming negligible reciprocal field size, DDH, and efficiency of the two exact clock-normalized fair-bit reductions. | **Reconcile.** These are separate security notions and proofs. The revised computational completion includes an external uniform-efficiency argument; it is not a Lean construction of every reduction machine or a theorem transferring the symbolic result. [S1, C6, C9, C10] |

## Consequences for a future common model

These existing differences do not reopen the completed revised computational
result or add requirements to this publication increment.

A shared model must first choose the repair predicate, rejection behavior and
public observation schedule. Those are protocol choices, not notation. It must
also specify which concrete identities, scalar operations and proof fields are
represented by the symbolic signature. The existing symbolic identity omission
cannot justify excluding the concrete neutral ciphertext; the
[repair discrepancy](helios-repair-ambiguity.md) remains explicit.

Election-size and corruption parameters require separate alignment. Instantiating
the symbolic theorem at two candidates and one extra voter narrows its size,
but does not change its rejection or publication semantics. Conversely, generic
computational ballot definitions do not establish a final theorem for arbitrary
voter/candidate counts or corrupt trustees.

The checked callback normalization in `ElectionSecurityFamily.coverage` preserves
the original computational game; `run_coverage` also preserves its persistent
cache output. These are internal computational equalities. The encoders in
`ElectionPublicEncoding` retain every public field and agree with the existing
prime codecs. Neither result relates those records to symbolic frames. The
external efficiency assumptions and conclusion are recorded in the
[closing audit](helios-computational-closing-audit.md); publication updates that
record alongside the final theorem. This comparison adds no theorem or security
assumption.

## Declaration anchors

All source paths below are repository files. The tables cite definitions as model
evidence and the named conclusions as theorem evidence; definitions alone are
not security proofs.

| Anchor | Source and exact declarations |
| --- | --- |
| S1 | [Symbolic/SourceBallotSecrecy.lean](../../ExplainableCrypto/Helios/Symbolic/SourceBallotSecrecy.lean): `Named.IsWeakLabelledBisimulation`, `Named.WeakLabelledBisimilar`, `scopedVoterElection_ballot_secrecy`. Full namespace prefix: `ExplainableCrypto.Helios.Symbolic.Historical.General.Source`. |
| S2 | [Symbolic/HistoricalFrames.lean](../../ExplainableCrypto/Helios/Symbolic/HistoricalFrames.lean): `Historical.Names`, `Historical.Names.Fresh`; [Symbolic/SourceScopedVoterElection.lean](../../ExplainableCrypto/Helios/Symbolic/SourceScopedVoterElection.lean): `scopedElectionBody`, `scopedVoterElection`, `administration_nonce_policy`. |
| S3 | [Symbolic/CandidateSubstitutions.lean](../../ExplainableCrypto/Helios/Symbolic/CandidateSubstitutions.lean): `CandidateSubstitution`, `BitCandidate`, `CandidateSubstitution.bit_representative`. |
| S4 | [Symbolic/Ballot.lean](../../ExplainableCrypto/Helios/Symbolic/Ballot.lean): `ProofValid`, `NoReuse`, `PrintedGuard`, `TailGuard`, `Accepted`, `oneCandidate_printed_rejects`, `oneCandidate_corrected_accepts`. |
| S5 | [Symbolic/Terms.lean](../../ExplainableCrypto/Helios/Symbolic/Terms.lean): `Constant`, `Unary`, `Binary`, `Ternary`, `Term`, `Term.Public`; [Symbolic/Equations.lean](../../ExplainableCrypto/Helios/Symbolic/Equations.lean): `AC`, `Equation`, `EqE`. |
| S6 | [Symbolic/HistoricalProcessSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/HistoricalProcessSyntax.lean): `Process.Phase`, `Process.Action`, `Process.Step`, `Process.Reachable`; the final action relation is S1, not only this normalized stage model. |
| S7 | [Symbolic/SourceElectionSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourceElectionSyntax.lean): `Channels`, `publishBody`, `boardFinish`, `collectBallots`, `boardStart`, `trusteeAgent`, `electionBody`. |
| S8 | [Symbolic/SourceCapturedViews.lean](../../ExplainableCrypto/Helios/Symbolic/SourceCapturedViews.lean): `sourceView`, `sourceState`, `reachable_source_view_staticEq`; [Symbolic/SourcePayloadSyntax.lean](../../ExplainableCrypto/Helios/Symbolic/SourcePayloadSyntax.lean): `trusteeBody`, `resultBody`, `sourceTallies`, `sourcePartials`, `sourceResults`, `sourceFinalFrame`. |
| S9 | [Symbolic/SharedTally.lean](../../ExplainableCrypto/Helios/Symbolic/SharedTally.lean): `accepted_sequence_tally_numeric`. |
| C1 | [Computational/AttackGame.lean](../../ExplainableCrypto/Helios/Computational/AttackGame.lean): `PublicParameters`, `PublicPrefix`, `PublicResult`, `decodeBounded`; [Computational/Board.lean](../../ExplainableCrypto/Helios/Computational/Board.lean): `BoardEntry`, `Decision`, `boardTally`. |
| C2 | [Computational/ElectionOracle.lean](../../ExplainableCrypto/Helios/Computational/ElectionOracle.lean): `ElectionOracle.Adversary`, `prefixWithCoins`, `finishWithCoins`, `world`, `game`, `preparedGame`, `run`. |
| C3 | [Computational/StrongBallot.lean](../../ExplainableCrypto/Helios/Computational/StrongBallot.lean): `Proof01.StrongValid`, `Ballot.StrongValid`, `Ballot.coveredCiphertext`, `Ballot.ExpandedFreshFor`, `strongHonestBallot`, `copied_aggregate_not_expanded_fresh`. |
| C4 | [Computational/RepairedExecution.lean](../../ExplainableCrypto/Helios/Computational/RepairedExecution.lean): `StrongCryptoHashes`, `strongKeyProof`, `strongPartialProof`, `makeRepairedPrefix`, `finishRepairedElection`, `executeRepairedAttack_rejected`; [Computational/Trustee.lean](../../ExplainableCrypto/Helios/Computational/Trustee.lean): `SchnorrProof`, `partialProof`. |
| C5 | [Computational/BallotProof.lean](../../ExplainableCrypto/Helios/Computational/BallotProof.lean): `encryptWith`, `Branch`, `Proof01`, `neutralProof`; [Computational/HonestSampling.lean](../../ExplainableCrypto/Helios/Computational/HonestSampling.lean): nonzero honest sampling; [Computational/WeakProofMalleability.lean](../../ExplainableCrypto/Helios/Computational/WeakProofMalleability.lean): `Proof01.rerandomize_valid`. |
| C6 | [Computational/ElectionSecurityFamily.lean](../../ExplainableCrypto/Helios/Computational/ElectionSecurityFamily.lean): `Family`, `Family.prepared`, `Family.coverage`, `Family.run_coverage`, `Family.ballot_secrecy`; [Computational/ElectionClock.lean](../../ExplainableCrypto/Helios/Computational/ElectionClock.lean): `adversary`, `world_eq`. |
| C7 | [Computational/RepairedBoardOracle.lean](../../ExplainableCrypto/Helios/Computational/RepairedBoardOracle.lean): `strongBallotVerifyAllOracle`, `repairedSubmitOracle`, `repairedCastHonestPairWithCoinsOracle`. |
| C8 | [Computational/ElectionPublicBounds.lean](../../ExplainableCrypto/Helios/Computational/ElectionPublicBounds.lean): `support_prefix_shape`, `support_finish_shape`, `decodeBounded_le`; [Computational/ElectionPublicEncoding.lean](../../ExplainableCrypto/Helios/Computational/ElectionPublicEncoding.lean): `encodePrefix`, `encodeResult`, `prefix_injective`, `result_injective`, `prime_prefix_eq`, `prime_result_eq`. |
| C9 | [Computational/ElectionSecrecyFairBits.lean](../../ExplainableCrypto/Helios/Computational/ElectionSecrecyFairBits.lean): `main`, `reject`, `prepared_negligible_of_fair_bits`; [Computational/ElectionSecrecyConditional.lean](../../ExplainableCrypto/Helios/Computational/ElectionSecrecyConditional.lean): `prepared_negligible_of_native_coin_ddh`. |
| C10 | [Computational/ReductionEfficiency.lean](../../ExplainableCrypto/Helios/Computational/ReductionEfficiency.lean): `GroupRepresentation`, `Realization`, `MainReductionEfficient`, `RejectionReductionEfficient`, `DDHAssumption`. `Realization` requires whole finite coin-only code, all-path polynomial termination, actual coin readiness and exact output law; the secrecy theorem retains the two efficiency hypotheses. |
