import ExplainableCrypto.Helios.Computational.BallotSigmaSimulation
import ExplainableCrypto.Helios.Computational.CollisionProbability

/-! Statistical bridge from the actual nonzero sampler to the full field.
Refilling a zero uniform draw with an independent nonzero draw preserves the
nonzero distribution and couples it to uniform with failure probability 1/|F|. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

noncomputable def nonzeroRefill (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] : ProbComp F := do
  let x ← uniformSample F
  if x = 0 then sampleNonzero F else pure x

omit [DecidableEq F] [SampleableType F] in
private theorem refill_mass_identity :
    ((Fintype.card F : ENNReal)⁻¹ * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ +
      (Fintype.card F : ENNReal)⁻¹) = ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ := by
  have hn : 1 < Fintype.card F := Fintype.one_lt_card
  have hpos : (Fintype.card F : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hpred : ((Fintype.card F - 1 : Nat) : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hn)
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  have hreal : (1 : ℝ) < Fintype.card F := by exact_mod_cast hn
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
  norm_num
  field_simp [ne_of_gt (lt_trans zero_lt_one hreal), sub_ne_zero.mpr (ne_of_gt hreal)]
  ring

/-- The refill construction has exactly the distribution of the historical sampler. -/
theorem nonzeroRefill_eq : 𝒮[nonzeroRefill F] = 𝒮[sampleNonzero F] := by
  apply evalSPMF_ext
  intro y
  unfold nonzeroRefill
  rw [probOutput_bind_eq_tsum]
  by_cases hy : y = 0
  · subst y
    have hz : Pr[= (0 : F) | sampleNonzero F] = 0 :=
      probOutput_eq_zero_of_not_mem_support (fun h => sampleNonzero_ne_zero h rfl)
    rw [hz]
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = 0
    · subst x; simp [hz]
    · simp [hx, Ne.symm hx, probOutput_pure]
  · have hpoint : Pr[= y | sampleNonzero F] = ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ :=
      sampleNonzero_probability (Units.mk0 y hy)
    have he (x : F) : Pr[= x | uniformSample F] *
        Pr[= y | (if x = 0 then sampleNonzero F else pure x)] =
        (if x = 0 then (Fintype.card F : ENNReal)⁻¹ *
          ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ else 0) +
        (if x = y then (Fintype.card F : ENNReal)⁻¹ else 0) := by
      by_cases hx : x = 0
      · subst x
        simp [Ne.symm hy, hpoint]
      · by_cases hxy : x = y
        · subst x; simp [hy, probOutput_pure]
        · simp [hx, hxy, Ne.symm hxy, probOutput_pure]
    simp_rw [he]
    rw [ENNReal.tsum_add]
    simpa only [tsum_ite_eq, hpoint] using (refill_mass_identity (F := F))

theorem sampleNonzero_uniform_tv_le :
    tvDist (sampleNonzero F) (uniformSample F) ≤ (Fintype.card F : ℝ)⁻¹ := by
  have h := tvDist_bind_left_event_le (uniformSample F)
    (fun x => if x = 0 then sampleNonzero F else pure x) (fun x => pure x)
    (fun x => x = 0) (by intro x hx; simp [hx])
  have he : tvDist (nonzeroRefill F) (uniformSample F) =
      tvDist (sampleNonzero F) (uniformSample F) := by
    unfold tvDist
    rw [nonzeroRefill_eq]
  rw [← he]
  simpa only [nonzeroRefill, bind_pure, probEvent_eq_eq_probOutput,
    probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast] using h

/-- Replacing the three historical proof coins by full-field coins costs at
most three times the single-draw bound, for any common continuation. -/
theorem three_nonzero_draws_tv_le {α : Type} (f : F → F → F → ProbComp α) :
    tvDist (do let w ← sampleNonzero F; let e ← sampleNonzero F; let z ← sampleNonzero F; f w e z)
      (do let w ← uniformSample F; let e ← uniformSample F; let z ← uniformSample F; f w e z) ≤
      3 * (Fintype.card F : ℝ)⁻¹ := by
  let d : ℝ := (Fintype.card F : ℝ)⁻¹
  have step (a b : F → ProbComp α) (c : ℝ) (hab : ∀ x, tvDist (a x) (b x) ≤ c) :
      tvDist (sampleNonzero F >>= a) (uniformSample F >>= b) ≤ c + d := by
    calc
      _ ≤ tvDist (sampleNonzero F >>= a) (sampleNonzero F >>= b) +
          tvDist (sampleNonzero F >>= b) (uniformSample F >>= b) := tvDist_triangle _ _ _
      _ ≤ c + d := add_le_add (tvDist_bind_left_le_const' _ _ _ c hab)
        ((tvDist_bind_right_le b _ _).trans sampleNonzero_uniform_tv_le)
  refine (step _ _ (2*d) ?_).trans (by dsimp [d]; linarith)
  intro w
  refine (step _ _ d ?_).trans (by linarith)
  intro e
  simpa using step (fun z => f w e z) (fun z => f w e z) 0 (fun z => by simp)

variable {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Honest-verifier simulation for the actual nonzero-coin protocol, with an
explicit statistical loss. This does not assert adaptive Fiat–Shamir security. -/
theorem ballotSigma_hvzk :
    (ballotSigma (F := F) (G := G)).HVZK ballotFullSimTranscript
      (3 * (Fintype.card F : ℝ)⁻¹) := by
  intro stmt wit hw
  have he := ballotSigma_full_hvzk (F := F) (G := G) stmt wit hw
  calc
    _ = tvDist ((ballotSigma (F := F) (G := G)).realTranscript stmt wit)
        ((ballotSigmaWithSampler (G := G) (uniformSample F)).realTranscript stmt wit) := by
      unfold tvDist
      rw [he]
    _ ≤ _ := by
      simp only [ChallengeVerifyProtocol.realTranscript, ballotSigma, ballotSigmaWithSampler, monad_norm]
      exact three_nonzero_draws_tv_le _

#print axioms three_nonzero_draws_tv_le
#print axioms ballotSigma_hvzk
#print axioms nonzeroRefill_eq
#print axioms sampleNonzero_uniform_tv_le

end ExplainableCrypto.Helios.Computational
