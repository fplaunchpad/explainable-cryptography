import ExplainableCrypto.Helios.Computational.ElectionSecrecyPrototype
import ExplainableCrypto.Helios.Computational.FairBitUniformOracle
import Mathlib.Analysis.SpecificLimits.Normed

/-! Fair-bit sampling transport for the exact DDH reductions. Only adversary
randomness is replaced; the pinned real/random challenge distributions stay
unchanged. Local operations and standard-PPT efficiency are not asserted. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHFairBits
open OracleComp OracleSpec Filter Topology Asymptotics ElectionDDHSource

/-- Express the existing coin-only implementation through the pinned ProbComp
interface. `uniformSampleImpl` uses the uniform Boolean sampler at each coin. -/
def bits {A : Type} (slack : Nat) (oa : ProbComp A) : ProbComp A :=
  simulateQ uniformSampleImpl (runFairBitUniform slack oa)

theorem bits_law {A : Type} (slack : Nat) (oa : ProbComp A) :
    evalSPMF (bits slack oa) = evalSPMF (runFairBitUniform slack oa) :=
  uniformSampleImpl.evalSPMF_simulateQ _

private theorem bits_distance {A : Type} (slack : Nat) (oa : ProbComp A)
    (B : Nat) (hb : oa.IsTotalQueryBound B) :
    tvDist (bits slack oa) oa ≤ (B:ℝ)*((2:ℝ)^slack)⁻¹ := by
  simpa only [tvDist, bits_law] using runFairBitUniform_tv_le slack oa B hb

/-- Same public DDH input; replace only the reduction's private sampling. -/
def reduction {F G : Type} (slack : Nat) (D : DiffieHellman.DDHAdversary F G) :
    DiffieHellman.DDHAdversary F G := fun g A B T => bits slack (D g A B T)

section Finite
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [SampleableType F]

/-- Full real-DDH output law: challenge sampling is shared exactly. -/
theorem real_distance (slack : Nat) (g : G) (D : DiffieHellman.DDHAdversary F G)
    (B : Nat) (hb : ∀ A T U, (D g A T U).IsTotalQueryBound B) :
    tvDist (DiffieHellman.ddhExpReal g (reduction slack D))
      (DiffieHellman.ddhExpReal g D) ≤ (B:ℝ)*((2:ℝ)^slack)⁻¹ := by
  unfold DiffieHellman.ddhExpReal
  apply tvDist_bind_left_le_const'
  intro a
  apply tvDist_bind_left_le_const'
  intro b
  exact bits_distance slack _ B (hb _ _ _)

/-- Full random-DDH output law, with the third exact challenge sample retained. -/
theorem random_distance (slack : Nat) (g : G) (D : DiffieHellman.DDHAdversary F G)
    (B : Nat) (hb : ∀ A T U, (D g A T U).IsTotalQueryBound B) :
    tvDist (DiffieHellman.ddhExpRand g (reduction slack D))
      (DiffieHellman.ddhExpRand g D) ≤ (B:ℝ)*((2:ℝ)^slack)⁻¹ := by
  unfold DiffieHellman.ddhExpRand
  apply tvDist_bind_left_le_const'
  intro a
  apply tvDist_bind_left_le_const'
  intro b
  apply tvDist_bind_left_le_const'
  intro c
  exact bits_distance slack _ B (hb _ _ _)

/-- Both world's errors contribute to the actual two-game advantage. -/
theorem advantage_distance (slack : Nat) (g : G) (D : DiffieHellman.DDHAdversary F G)
    (B : Nat) (hb : ∀ A T U, (D g A T U).IsTotalQueryBound B) :
    |DiffieHellman.ddhDistAdvantage g (reduction slack D) -
      DiffieHellman.ddhDistAdvantage g D| ≤ 2*(B:ℝ)*((2:ℝ)^slack)⁻¹ := by
  have hr := (abs_probOutput_toReal_sub_le_tvDist
    (DiffieHellman.ddhExpReal g (reduction slack D)) (DiffieHellman.ddhExpReal g D)).trans (real_distance slack g D B hb)
  have hn := (abs_probOutput_toReal_sub_le_tvDist
    (DiffieHellman.ddhExpRand g (reduction slack D)) (DiffieHellman.ddhExpRand g D)).trans (random_distance slack g D B hb)
  unfold DiffieHellman.ddhDistAdvantage
  apply (abs_abs_sub_abs_le_abs_sub _ _).trans
  have ht := abs_sub_le
    ((Pr[= true | DiffieHellman.ddhExpReal g (reduction slack D)]).toReal-
      (Pr[= true | DiffieHellman.ddhExpReal g D]).toReal) 0
    ((Pr[= true | DiffieHellman.ddhExpRand g (reduction slack D)]).toReal-
      (Pr[= true | DiffieHellman.ddhExpRand g D]).toReal)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  have he : ∀ a b c d : ℝ, (a-b)-(c-d) = (a-c)-(b-d) := by intros; ring
  rw [he]
  linarith only [ht, hr, hn]

end Finite

/-- Linear statistical slack n yields negligible sampler error per range query. -/
theorem sampler_negligible : negligible (fun n => ((2:ENNReal)^n)⁻¹) := by
  apply (negligible_iff_superpolynomialDecay_toReal (fun n => by simp)).mpr
  intro k
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1:ℝ) < 2)

section Families
variable {F G : Nat → Type} [∀ n, Field (F n)] [∀ n, AddCommGroup (G n)]
  [∀ n, Module (F n) (G n)] [∀ n, SampleableType (F n)]

/-- Transfer security of the fair-bit algorithm in the exact DDH games back to
the ideal-range reduction. This derives sampling loss; query budgets still do
not certify local runtime or effective group operations. -/
theorem negligible_of_bits (g : ∀ n, G n) (D : ∀ n, DiffieHellman.DDHAdversary (F n) (G n))
    (B : Nat → Nat) (P : Polynomial Nat) (hpoly : ∀ n, B n ≤ P.eval n)
    (hquery : ∀ n A T U, (D n (g n) A T U).IsTotalQueryBound (B n))
    (hbits : negligible (fun n => ENNReal.ofReal
      (DiffieHellman.ddhDistAdvantage (g n) (reduction n (D n))))) :
    negligible (fun n => ENNReal.ofReal (DiffieHellman.ddhDistAdvantage (g n) (D n))) := by
  have hc : negligible (fun n => ((2^n:Nat):ENNReal)⁻¹) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using sampler_negligible
  have he := negligible_ofReal_natDiv_of_poly_bound hc
    (g := fun n => 2*B n) (p := 2*P) (by
      intro n
      simpa using Nat.mul_le_mul_left 2 (hpoly n))
  have herr : negligible (fun n => ENNReal.ofReal (2*(B n:ℝ)*((2:ℝ)^n)⁻¹)) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using he
  apply negligible_of_le _ (negligible_ofReal_add hbits herr)
  intro n
  apply ENNReal.ofReal_le_ofReal
  have h := (abs_le.mp (advantage_distance n (g n) (D n) (B n) (hquery n))).1
  linarith only [h]

end Families
end ExplainableCrypto.Helios.Computational.ElectionDDHFairBits
