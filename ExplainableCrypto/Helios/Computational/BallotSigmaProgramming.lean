import ExplainableCrypto.Helios.Computational.BallotSigmaSimulation

/-! Distribution prerequisites for programming the actual strong ballot proof.
The point bound requires an injective generator. Conditional challenge uniformity
requires a valid statement, and uses the full-field reference equality only;
the historical nonzero simulation loss remains a separate proved bound. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem uniform_injective_point_le (f : F → G) (hf : Function.Injective f) (target : G) :
    Pr[fun x => f x = target | uniformSample F] ≤ (Fintype.card F : ENNReal)⁻¹ := by
  by_cases h : ∃ x, f x = target
  · obtain ⟨x, rfl⟩ := h
    simpa only [hf.eq_iff, probEvent_eq_eq_probOutput, probOutput_uniformSample] using
      (le_refl ((Fintype.card F : ENNReal)⁻¹))
  · have he : ∀ x, ¬ f x = target := by simpa using h
    simp [he]

omit [DecidableEq F] in
/-- A fixed simulated commitment is unlikely for every ciphertext statement,
provided the protocol generator has injective exponentiation. -/
theorem ballotSim_commit_probability_le (stmt : BallotStatement G)
    (hg : Function.Injective (fun r : F => r • stmt.generator)) (pc : BallotCommitment G) :
    Pr[fun t => t.1 = pc | ballotFullSimTranscript (F := F) stmt] ≤
      (Fintype.card F : ENNReal)⁻¹ := by
  refine (probEvent_mono (q := fun t => t.1.1.1 = pc.1.1)
    (fun _ _ h => congrArg (fun x : BallotCommitment G => x.1.1) h)).trans ?_
  unfold ballotFullSimTranscript
  refine probEvent_bind_le_of_forall_le fun c _ => ?_
  refine probEvent_bind_le_of_forall_le fun e _ => ?_
  rw [probEvent_bind_bind_swap]
  refine probEvent_bind_le_of_forall_le fun z₁ _ => ?_
  simpa [Function.comp_def, ballotSimCommit, simulatedBranch] using
    uniform_injective_point_le (fun z : F => z • stmt.generator - e • stmt.ciphertext.1)
      (fun x y he => hg (by simpa using congrArg (fun v : G => v + e • stmt.ciphertext.1) he)) pc.1.1

omit [DecidableEq F] in
/-- Collision with an existing finite strong-hash query domain. The domain may
contain other statements; the complete statement remains part of the key. -/
theorem ballotSim_query_collision_le (stmt : BallotStatement G)
    (hg : Function.Injective (fun r : F => r • stmt.generator))
    (queries : Finset (BallotStatement G × BallotCommitment G)) :
    Pr[fun t => (stmt,t.1) ∈ queries | ballotFullSimTranscript (F := F) stmt] ≤
      queries.card * (Fintype.card F : ENNReal)⁻¹ := by
  classical
  induction queries using Finset.induction_on with
  | empty => simp
  | @insert key queries hk ih =>
    simp only [Finset.mem_insert]
    have hb : Pr[fun t => (stmt,t.1) = key | ballotFullSimTranscript (F := F) stmt] ≤
        (Fintype.card F : ENNReal)⁻¹ :=
      (probEvent_mono (fun _ _ h => congrArg Prod.snd h)).trans
        (ballotSim_commit_probability_le stmt hg key.2)
    calc
      _ ≤ Pr[fun t => (stmt,t.1) = key | ballotFullSimTranscript (F := F) stmt] +
          Pr[fun t => (stmt,t.1) ∈ queries | ballotFullSimTranscript (F := F) stmt] :=
        probEvent_or_le _ _ _
      _ ≤ (Fintype.card F : ENNReal)⁻¹ + queries.card * (Fintype.card F : ENNReal)⁻¹ :=
        add_le_add hb ih
      _ = _ := by rw [Finset.card_insert_of_notMem hk]; push_cast; ring

/-- The simulator challenge is uniform conditional on the commitment, on every
statement admitting a bit/nonce witness. This is VCVio's exact companion property. -/
theorem ballotSigma_simChalUniformGivenCommit :
    (ballotSigma (F := F) (G := G)).simChalUniformGivenCommit ballotFullSimTranscript := by
  intro stmt wit hw pc c₀
  have he := ballotSigma_full_hvzk (F := F) (G := G) stmt wit hw
  rw [probEvent_congr' (fun _ _ => Iff.rfl) he.symm,
    probEvent_congr' (fun _ _ => Iff.rfl) he.symm]
  simp only [ChallengeVerifyProtocol.realTranscript, ballotSigmaWithSampler, monad_norm]
  simp only [probEvent_bind_eq_tsum]
  simp only [← ENNReal.tsum_mul_right, mul_assoc]
  apply tsum_congr
  intro w
  congr 1
  apply tsum_congr
  intro e
  congr 1
  apply tsum_congr
  intro z
  congr 1
  by_cases hp : ballotCommitWith stmt wit (w,e,z) = pc
  · simp only [probEvent_pure, hp, true_and, if_true]
    simp only [probOutput_uniformSample, mul_ite, mul_one, mul_zero]
    simp only [tsum_ite_eq, ENNReal.tsum_const, ENat.card_eq_coe_fintype_card,
      ENat.toENNReal_coe]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero (α := F))
      (ENNReal.natCast_ne_top _), one_mul]
    simp only [one_mul]
  · simp [probEvent_pure, hp]

#print axioms ballotSim_commit_probability_le
#print axioms ballotSigma_simChalUniformGivenCommit
#print axioms ballotSim_query_collision_le

end ExplainableCrypto.Helios.Computational
