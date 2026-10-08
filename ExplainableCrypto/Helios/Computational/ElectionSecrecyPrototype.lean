import ExplainableCrypto.Helios.Computational.ElectionDDHReduction
import VCVio.CryptoFoundations.Asymptotics.Negligible
import Mathlib.Analysis.SpecificLimits.Basic

/-! Conditional asymptotic assembly of the actual finite election reduction.
The DDH premises concern the exact reductions. Their standard-PPT efficiency
and coverage of the intended election families remain separate obligations. -/
namespace ExplainableCrypto.Helios.Computational.ElectionSecrecyPrototype
open Filter Topology Asymptotics OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionDDHSource

/-- Each fixed accuracy degree selects a polynomial, not exponential, request. -/
def accuracy (k n : Nat) : Nat := (n+1)^(k+1)

theorem accuracy_pos (k n : Nat) : 0 < accuracy k n := by
  simp [accuracy]

/-- The actual replay count remains a polynomial for each fixed accuracy degree
and polynomial live-query budget. This says nothing about local runtime. -/
theorem replay_polynomial (P : Polynomial Nat) (k : Nat) :
    ∃ R : Polynomial Nat, ∀ n,
      ballotReplayTrials (P.eval n) (accuracy k n) = R.eval n := by
  refine ⟨3456*(P+1)^3*((Polynomial.X+1)^(k+1))^4, ?_⟩
  intro n
  simp [ballotReplayTrials, accuracy]

private theorem scaled_slack (k n : Nat) :
    (n:ℝ)^k * (2*(accuracy k n:ℝ)⁻¹) ≤ 2/((n:ℝ)+1) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hp : (n:ℝ)^k ≤ ((n:ℝ)+1)^k := by gcongr; linarith
  calc
    _ ≤ ((n:ℝ)+1)^k * (2*(accuracy k n:ℝ)⁻¹) := by gcongr
    _ = _ := by
      dsimp [accuracy]
      push_cast
      rw [pow_succ]
      field_simp

/-- A separate negligible error for every fixed polynomial accuracy suffices.
No single inverse-polynomial slack is asserted to be negligible. -/
theorem negligible_of_polynomial_accuracy {bias : Nat → ℝ} {err : Nat → Nat → ℝ}
    (hb : ∀ n, 0 ≤ bias n)
    (herr : ∀ k, SuperpolynomialDecay atTop (Nat.cast : Nat → ℝ) (err k))
    (hbound : ∀ k, ∀ᶠ n in atTop,
      bias n ≤ err k n + 2*(accuracy k n:ℝ)⁻¹) :
    negligible (fun n => ENNReal.ofReal (bias n)) := by
  apply (negligible_ofReal_iff hb).mpr
  intro k
  have ht : Tendsto (fun n : Nat => (n:ℝ)^k * err k n + 2/((n:ℝ)+1))
      atTop (𝓝 0) := by
    have hs := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simpa only [mul_zero, add_zero, div_eq_mul_inv, one_mul] using (herr k k).add hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall fun n => mul_nonneg (by positivity) (hb n)
  · filter_upwards [hbound k] with n hn
    have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ (n:ℝ)^k by positivity)
    rw [mul_add] at hm
    exact hm.trans (add_le_add le_rfl (scaled_slack k n))

section Families
variable {F G : Nat → Type} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)] [∀ n, SampleableType (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)] [∀ n, DecidableEq (G n)]

/-- Parameter families of the existing prepared election. The preparation,
attacker and full public-view game are retained pointwise. Query bounds are
explicit; no local execution or efficient-family certificate is hidden here. -/
structure PreparedFamily (F G : Nat → Type) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] [∀ n, SampleableType (F n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)] [∀ n, DecidableEq (G n)] where
  Init : Nat → Type
  Saved : Nat → Type
  fingerprint : ∀ n, PublicParameters (F n) (G n) → Nat
  generator : ∀ n, G n
  generator_injective : ∀ n, Function.Injective (fun r : F n => r • generator n)
  prepare : ∀ n, Comp (F n) (G n) (Init n)
  adversary : ∀ n, Init n → Adversary (F n) (G n) (Saved n)
  p : Nat → Nat
  c : Nat → Nat
  prepare_hash : ∀ n, (prepare n).IsQueryBoundP (ElectionCacheBudget.isHash (F := F n)) (p n)
  cast_hash : ∀ n initial before, ((adversary n initial).castBallot before).IsQueryBoundP
    (ElectionCacheBudget.isHash (F := F n)) (c n)

variable (D : PreparedFamily F G)

/-- Polynomial domination for the actual family's replay count. The polynomial
may depend on the attacker budget and the fixed accuracy degree. -/
theorem replay_bounded (P : Polynomial Nat)
    (hbudget : ∀ n, D.p n+D.c n ≤ P.eval n) (k : Nat) :
    ∃ R : Polynomial Nat, ∀ n,
      ballotReplayTrials (D.p n+D.c n+9) (accuracy k n) ≤ R.eval n := by
  obtain ⟨R, hR⟩ := replay_polynomial (P+9) k
  refine ⟨R, fun n => ?_⟩
  rw [← hR]
  unfold ballotReplayTrials
  gcongr
  simpa using Nat.add_le_add_right (hbudget n) 9

/-- Bias in the original prepared game, including its shared oracle cache. -/
noncomputable def bias (n : Nat) : ℝ :=
  |(Pr[fun out => out.1 = true |
    run (preparedGame (D.fingerprint n) (D.generator n) (D.prepare n) (D.adversary n)) ∅]).toReal-1/2|

/-- Advantage of the exact public DDH test at polynomial accuracy degree k. -/
noncomputable def mainAdvantage (k n : Nat) : ℝ :=
  DiffieHellman.ddhDistAdvantage (D.generator n)
    (ballotSecrecyDistinguisher (D.fingerprint n) (D.prepare n) (D.adversary n)
      (D.p n+D.c n+9) (accuracy k n))

/-- The second actual DDH test observes honest rejection. -/
noncomputable def rejectionAdvantage (n : Nat) : ℝ :=
  DiffieHellman.ddhDistAdvantage (D.generator n)
    (honestRejectDistinguisher (D.fingerprint n) (D.prepare n) (D.adversary n))

private noncomputable def algebraicError (n : Nat) : ℝ :=
  18*(noncePointBound (F n)).toReal +
    3*((11*(D.p n:ℝ)+2*D.c n+131)/(Fintype.card (F n):ℝ))

omit [∀ n, Field (F n)] [∀ n, DecidableEq (F n)] [∀ n, SampleableType (F n)] in
private theorem card_negligible
    (hsize : negligible (fun n => noncePointBound (F n))) :
    negligible (fun n => (Fintype.card (F n):ENNReal)⁻¹) := by
  apply negligible_of_le _ hsize
  intro n
  simp only [noncePointBound]
  gcongr
  exact Nat.sub_le _ _

private theorem algebraic_negligible (P : Polynomial Nat)
    (hbudget : ∀ n, D.p n+D.c n ≤ P.eval n)
    (hsize : negligible (fun n => noncePointBound (F n))) :
    SuperpolynomialDecay atTop (Nat.cast : Nat → ℝ) (algebraicError D) := by
  have hnonce : SuperpolynomialDecay atTop (Nat.cast : Nat → ℝ)
      (fun n => (noncePointBound (F n)).toReal) := by
    apply (negligible_iff_superpolynomialDecay_toReal _).mp hsize
    intro n
    simp only [noncePointBound, ENNReal.inv_ne_top]
    have h := Fintype.one_lt_card (α := F n)
    exact_mod_cast (by omega : Fintype.card (F n)-1 ≠ 0)
  have hr := negligible_ofReal_natDiv_of_poly_bound (card_negligible hsize)
    (p := 11*P+131) (g := fun n => 11*D.p n+2*D.c n+131) (by
      intro n
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
      have h := hbudget n
      omega)
  have hfrac : SuperpolynomialDecay atTop (Nat.cast : Nat → ℝ)
      (fun n => (11*(D.p n:ℝ)+2*D.c n+131)/(Fintype.card (F n):ℝ)) := by
    apply (negligible_ofReal_iff (fun n => by positivity)).mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hr
  exact (hnonce.const_mul 18).add (hfrac.const_mul 3)

/-- The finite reduction's field-size side condition follows eventually from
the family size and query-budget premises, for every fixed accuracy degree. -/
theorem accuracy_admissible (P : Polynomial Nat)
    (hbudget : ∀ n, D.p n+D.c n ≤ P.eval n)
    (hsize : negligible (fun n => noncePointBound (F n))) (k : Nat) :
    ∀ᶠ n in atTop, 12*(D.p n+D.c n+10)*accuracy k n ≤ Fintype.card (F n) := by
  have hr := negligible_ofReal_natDiv_of_poly_bound (card_negligible hsize)
    (p := 12*(P+10)*(Polynomial.X+1)^(k+1))
    (g := fun n => 12*(D.p n+D.c n+10)*accuracy k n) (by
      intro n
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, accuracy]
      gcongr
      exact hbudget n)
  have hreal := (negligible_ofReal_iff (fun n => by positivity)).mp hr
  have ht : Tendsto (fun n =>
      (12*(D.p n+D.c n+10)*accuracy k n:Nat)/(Fintype.card (F n):ℝ)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using hreal 0
  filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with n hn
  have hq : (0:ℝ) < Fintype.card (F n) := by exact_mod_cast Fintype.card_pos
  have he := (div_lt_one hq).mp hn
  exact_mod_cast he.le

/-- Conditional completion prototype. The original election bias is negligible
provided the exact main reduction is DDH-secure for every fixed polynomial
accuracy degree and the exact honest-rejection test is DDH-secure. Deriving
these premises from standard DDH hardness requires the still-open efficiency
proofs; intended standard-PPT coverage is not asserted by this theorem. -/
theorem prepared_negligible_of_ddh (P : Polynomial Nat)
    (hbudget : ∀ n, D.p n+D.c n ≤ P.eval n)
    (hsize : negligible (fun n => noncePointBound (F n)))
    (hmain : ∀ k, negligible (fun n => ENNReal.ofReal (mainAdvantage D k n)))
    (hreject : negligible (fun n => ENNReal.ofReal (rejectionAdvantage D n))) :
    negligible (fun n => ENNReal.ofReal (bias D n)) := by
  apply negligible_of_polynomial_accuracy (err := fun k n =>
    algebraicError D n + mainAdvantage D k n + rejectionAdvantage D n)
  · intro n
    exact abs_nonneg _
  · intro k
    have hm := (negligible_ofReal_iff (fun n => abs_nonneg _)).mp (hmain k)
    have hr := (negligible_ofReal_iff (fun n => abs_nonneg _)).mp hreject
    exact ((algebraic_negligible D P hbudget hsize).add hm).add hr
  · intro k
    filter_upwards [accuracy_admissible D P hbudget hsize k] with n hn
    have h := prepared_ballot_secrecy_ddh_bound (D.fingerprint n) (D.generator n)
      (D.generator_injective n) (D.prepare n) (D.adversary n) (D.p n) (D.c n)
      (accuracy k n) (D.prepare_hash n) (D.cast_hash n) (accuracy_pos k n) hn
    change bias D n ≤ algebraicError D n + 2*(accuracy k n:ℝ)⁻¹ +
      mainAdvantage D k n + rejectionAdvantage D n at h
    linarith only [h]

end Families
end ExplainableCrypto.Helios.Computational.ElectionSecrecyPrototype
