import ExplainableCrypto.Helios.Computational.BallotReplayRepeat

/-! Effective integer parameters for the existing three-witness extractor.
The threshold is analysis-only; the algorithm computes a natural repetition count. -/
namespace ExplainableCrypto.Helios.Computational

/-- Executable repetition count for target extraction error at most `1/e`. -/
def ballotReplayTrials (N e : Nat) : Nat := 3456*(N+1)^3*e^4

private theorem geometric_reciprocal (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (k : Nat) :
    (1-t)^k ≤ (1+(k:ℝ)*t)⁻¹ := by
  have h : (1-t)^k*(1+(k:ℝ)*t) ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs : (1-t)*(1+((k:ℝ)+1)*t) ≤ 1+(k:ℝ)*t := by
        nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)+1 by positivity) (sq_nonneg t)]
      have hm := mul_le_mul_of_nonneg_left hs (pow_nonneg (sub_nonneg.mpr ht1) k)
      simp only [pow_succ, Nat.cast_succ] at *
      nlinarith
  simpa only [one_div] using (le_div_iff₀ (by positivity : 0 < 1+(k:ℝ)*t)).mpr h

private theorem parameters_real (N q e : Nat) (he : 0 < e) (hq : 12*(N+1)*e ≤ q) :
    3*((N:ℝ)+1)*(6*((N:ℝ)+1)*e)⁻¹ +
      (1-((6*((N:ℝ)+1)*e)⁻¹-(q:ℝ)⁻¹)^3)^(ballotReplayTrials N e) ≤ (e:ℝ)⁻¹ := by
  have he0 : (0:ℝ) < e := by exact_mod_cast he
  have he1 : (1:ℝ) ≤ e := by exact_mod_cast he
  have hn : (0:ℝ) < (N:ℝ)+1 := by positivity
  have hqr : 12*((N:ℝ)+1)*e ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le (by positivity) hqr
  let d : ℝ := 6*((N:ℝ)+1)*e
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hi : (q:ℝ)⁻¹ ≤ (2*d)⁻¹ := by
    apply inv_anti₀ (by positivity)
    dsimp [d]
    linarith
  have hhalf : (2*d)⁻¹ ≤ d⁻¹-(q:ℝ)⁻¹ := by
    have hh : d⁻¹ = 2*(2*d)⁻¹ := by field_simp
    linarith
  have hz : 0 ≤ d⁻¹-(q:ℝ)⁻¹ := le_trans (by positivity) hhalf
  have hu : d⁻¹-(q:ℝ)⁻¹ ≤ 1 := by
    have hi1 : d⁻¹ ≤ 1 := (inv_le_one₀ hd).mpr hd1
    linarith [inv_nonneg.mpr hq0.le]
  let t : ℝ := (d⁻¹-(q:ℝ)⁻¹)^3
  have ht : 0 ≤ t := pow_nonneg hz _
  have ht1 : t ≤ 1 := pow_le_one₀ hz hu
  have hl : ((2*d)⁻¹)^3 ≤ t := pow_le_pow_left₀ (by positivity) hhalf 3
  have hk : (ballotReplayTrials N e : ℝ)*((2*d)⁻¹)^3 = 2*e := by
    simp only [ballotReplayTrials, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    dsimp [d]
    field_simp
    ring
  have hkt : 2*(e:ℝ) ≤ (ballotReplayTrials N e : ℝ)*t := by
    rw [← hk]
    exact mul_le_mul_of_nonneg_left hl (by positivity)
  have htail : (1-t)^(ballotReplayTrials N e) ≤ (2*(e:ℝ))⁻¹ :=
    (geometric_reciprocal t ht ht1 _).trans (inv_anti₀ (by positivity) (by linarith))
  have hcontext : 3*((N:ℝ)+1)*d⁻¹ = (2*(e:ℝ))⁻¹ := by
    dsimp [d]
    field_simp
    ring
  have hsum : (2*(e:ℝ))⁻¹+(2*(e:ℝ))⁻¹ = (e:ℝ)⁻¹ := by field_simp; ring
  change 3*((N:ℝ)+1)*d⁻¹ + (1-t)^(ballotReplayTrials N e) ≤ _
  rw [hcontext, ← hsum]
  exact add_le_add le_rfl htail

/-- Explicit finite-field size and a positive integer accuracy request discharge
both the context and residual extraction losses. `e = 0` is excluded because
its extended-real target would be infinite. -/
theorem ballotReplay_parameters (N q e : Nat) (he : 0 < e) (hq : 12*(N+1)*e ≤ q) :
    3*(N+1 : ENNReal)*(6*(N+1)*e : ENNReal)⁻¹ +
      (1-((6*(N+1)*e : ENNReal)⁻¹-(q:ENNReal)⁻¹)^3)^(ballotReplayTrials N e) ≤
        (e:ENNReal)⁻¹ := by
  have he0 : (0:ℝ) < e := by exact_mod_cast he
  have he1 : (1:ℝ) ≤ e := by exact_mod_cast he
  have hqr : 12*((N:ℝ)+1)*e ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le (by positivity) hqr
  have hd : (0:ℝ) < 6*((N:ℝ)+1)*e := by positivity
  have hd1 : (1:ℝ) ≤ 6*((N:ℝ)+1)*e := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hu : (6*((N:ℝ)+1)*e)⁻¹-(q:ℝ)⁻¹ ≤ 1 := by
    have hi := (inv_le_one₀ hd).mpr hd1
    linarith [inv_nonneg.mpr hq0.le]
  have hz : 0 ≤ (6*((N:ℝ)+1)*e)⁻¹-(q:ℝ)⁻¹ := by
    apply sub_nonneg.mpr
    apply inv_anti₀ hd
    linarith
  have hpow : ((6*((N:ℝ)+1)*e)⁻¹-(q:ℝ)⁻¹)^3 ≤ 1 := by
    nlinarith [sq_nonneg ((6*((N:ℝ)+1)*e)⁻¹-(q:ℝ)⁻¹ + 1/2)]
  have h := ENNReal.ofReal_le_ofReal (parameters_real N q e he hq)
  rw [ENNReal.ofReal_add (by positivity) (pow_nonneg (by linarith) _),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by linarith),
    ENNReal.ofReal_sub _ (pow_nonneg hz 3), ENNReal.ofReal_pow hz,
    ENNReal.ofReal_sub _ (inv_nonneg.mpr hq0.le),
    ENNReal.ofReal_inv_of_pos hd, ENNReal.ofReal_inv_of_pos hq0,
    ENNReal.ofReal_inv_of_pos he0] at h
  simpa (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add,
    ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h

#print axioms ballotReplay_parameters
end ExplainableCrypto.Helios.Computational
