import ExplainableCrypto.Helios.Computational.ElectionRepairControl
import ExplainableCrypto.Helios.Computational.RepairControls

/-! Fixed modulo-23 transcripts and actual lazy-cache hit/miss controls.
Small scalar fields supply controls only, not a DDH hardness assumption. -/
namespace ExplainableCrypto.Helios.Computational.ElectionRepairControlControls
open OracleComp OracleSpec ElectionOracle
open RepairControls (Scalar hashes fixture)
open ExecutionControls (aliceCoins bobCoins)

private def before : PublicPrefix Scalar Scalar := (fixture false).beforeTally
private def neutralKey : Key Scalar := .ballot ⟨1, 3, (0, 0)⟩ ((1, 3), (1, 4))
private def submission (c : Scalar) : Ballot Scalar Scalar 2 :=
  repairedProofReuseSubmission {hashes with ballot := fun _ _ _ _ => c} before

/-- A cached neutral challenge is used once and is retained unchanged. -/
theorem neutral_hit :
    run (repairedReuseSubmission before) ((∅ : Cache Scalar Scalar).cacheQuery neutralKey 5) =
      pure (submission 5, (∅ : Cache Scalar Scalar).cacheQuery neutralKey 5) := by
  simp only [repairedReuseSubmission, run_bind, run_ask]
  change (do let out ← pure (5, (∅ : Cache Scalar Scalar).cacheQuery neutralKey 5)
             run (pure (proofReuse (fun _ => out.1) 1 3 1 1 1
               (strongHonestBallot hashes.ballot 1 3 false aliceCoins))) out.2) = _
  simp only [pure_bind, run_pure]
  rfl

/-- A missing neutral challenge is sampled and stored in that same cache. -/
theorem neutral_miss :
    run (repairedReuseSubmission before) (∅ : Cache Scalar Scalar) =
      (do let c ← uniformSample Scalar
          pure (submission c, (∅ : Cache Scalar Scalar).cacheQuery neutralKey c)) := by
  simp only [repairedReuseSubmission, run_bind, run_ask]
  change (do
    let out ← (do
      let c ← uniformSample Scalar
      pure (c, (∅ : Cache Scalar Scalar).cacheQuery neutralKey c))
    run (pure (proofReuse (fun _ => out.1) 1 3 1 1 1
      (strongHonestBallot hashes.ballot 1 3 false aliceCoins))) out.2) = _
  simp only [bind_assoc, pure_bind, run_pure]
  rfl

/-- Independent neutral transcript: challenge five splits as four plus one. -/
theorem neutral_transcript :
    (submission 5).ciphertext 1 = (0, 0) ∧
    ((submission 5).proof 1).zero.challenge = 4 ∧
    ((submission 5).proof 1).zero.response = 1 ∧
    ((submission 5).proof 1).one.challenge = 1 ∧
    ((submission 5).proof 1).one.response = 1 ∧
    (submission 5).overall = (strongHonestBallot hashes.ballot 1 3 false aliceCoins).overall := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl⟩

theorem sampled_rejection (vote : Bool) (cache : Cache Scalar Scalar) :
    Pr[fun out => out.1.decision = .reusedCiphertext |
      run (ElectionOracle.repairedAttackWorld hashes.fingerprint (1 : Scalar) vote) cache] = 1 :=
  repairedAttackWorld_rejected _ _ _ _

/-- Invalid proofs are rejected before the same reused ciphertext reaches weeding. -/
theorem invalid_before_reuse :
    let attack := (fixture false).submission
    let changed := {attack with overall := {attack.overall with zero :=
      {attack.overall.zero with response := attack.overall.zero.response + 1}}}
    (repairedSubmit hashes.ballot 1 3 2 before.board changed).1 = .invalidProof := by
  decide +kernel

/-- Preserve the independently derived counterfactual and honest acceptance control. -/
theorem repair_is_not_universal_rejection :
    (fixture false).beforeTally.honestDecisions = (.accepted, .accepted) ∧
    (fixture false).decodedTally 0 = some 1 ∧
    let a := strongHonestBallot hashes.ballot 1 3 false aliceCoins
    let b := strongHonestBallot hashes.ballot 1 3 true bobCoins
    (strongProofReuse hashes.ballot 1 3 1 1 1 a).FreshFor [a, b] := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.ElectionRepairControlControls
