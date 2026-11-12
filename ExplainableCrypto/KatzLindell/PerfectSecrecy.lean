import ExplainableCrypto.KatzLindell.Basic

/-!
# Perfect secrecy, and its equivalence with perfect indistinguishability

Definition 2.3 and the proof (left as Exercise 2.6 in the book) that it is
equivalent to Definition 2.6 (`PerfectlyIndistinguishable`).
-/

namespace ExplainableCrypto.KatzLindell

variable {M K C : Type}

/-- The distribution of the ciphertext when encrypting a fixed message `m`
under a freshly generated key. -/
noncomputable def ctDist (S : EncScheme M K C) (m : M) : PMF C :=
  S.keygen.bind (fun k => S.encrypt k m)

/-- **Definition 2.3.** `S` is perfectly secret if the ciphertext
distribution is the same no matter which of two messages was encrypted. -/
def PerfectSecrecy (S : EncScheme M K C) : Prop :=
  ∀ m₀ m₁ : M, ∀ c : C, ctDist S m₀ c = ctDist S m₁ c

/-- Swapping the order of summation over the key `k` and the ciphertext `c`,
when the `c`-sum is gated by a condition `P` that doesn't involve `k`. This
is the one non-algebraic step `privKeav_eq`'s proof needs (once per branch
of the challenge bit). -/
private theorem swap_sum (S : EncScheme M K C) (f : K → C → ENNReal) (P : C → Prop)
    [DecidablePred P] :
    (∑' k, S.keygen k * ∑' c, if P c then f k c else 0) =
      ∑' c, if P c then ∑' k, S.keygen k * f k c else 0 := by
  have step1 : ∀ k, S.keygen k * ∑' c, (if P c then f k c else 0) =
      ∑' c, if P c then S.keygen k * f k c else 0 := by
    intro k
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro c
    by_cases h : P c <;> simp [h]
  simp only [step1]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro c
  by_cases h : P c <;> simp [h]

/-- The success probability of *any* adversary against *any* scheme,
rewritten purely in terms of the two relevant ciphertext distributions.
Both directions of the equivalence with `PerfectSecrecy` boil down to this
one computation. -/
theorem privKeav_eq (S : EncScheme M K C) (A : Adversary M C) :
    PrivKeav S A true =
      2⁻¹ * (∑' c, ctDist S A.choose.2 c * (if A.guess c then 1 else 0) +
             ∑' c, ctDist S A.choose.1 c * (if A.guess c then 0 else 1)) := by
  simp [PrivKeav, ctDist, Bind.bind, Pure.pure, PMF.bind_apply, PMF.pure_apply,
    PMF.uniformOfFintype_apply, Fintype.card_bool, tsum_fintype]
  have distrib : ∀ (k : K) (x y : ENNReal), S.keygen k * (2⁻¹ * x + 2⁻¹ * y) =
      2⁻¹ * (S.keygen k * x) + 2⁻¹ * (S.keygen k * y) := fun k x y => by ring
  simp only [distrib]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_add,
    swap_sum S (fun a c => S.encrypt a A.choose.2 c) (fun c => A.guess c = true),
    swap_sum S (fun a c => S.encrypt a A.choose.1 c) (fun c => A.guess c = false)]
  congr 2
  apply tsum_congr
  intro c
  by_cases h : A.guess c <;> simp [h]

/-- **Forward direction of Exercise 2.6.** Perfect secrecy implies perfect
indistinguishability: if the ciphertext distribution can't tell `m₀` from
`m₁` at all, no adversary's guess can do better than a coin flip. -/
theorem PerfectSecrecy.perfectlyIndistinguishable {S : EncScheme M K C}
    (hS : PerfectSecrecy S) : PerfectlyIndistinguishable S := by
  intro A
  rw [privKeav_eq]
  simp only [hS A.choose.2 A.choose.1]
  have hcombine : ∀ c, ctDist S A.choose.1 c * (if A.guess c then 1 else 0) +
      ctDist S A.choose.1 c * (if A.guess c then 0 else 1) = ctDist S A.choose.1 c := by
    intro c
    by_cases h : A.guess c <;> simp [h]
  rw [← ENNReal.tsum_add]
  simp only [hcombine]
  rw [PMF.tsum_coe, mul_one, one_div]

/-- **Backward direction of Exercise 2.6.** If a scheme is *not* perfectly
secret, some pair of messages `m₀, m₁` yield different ciphertext
distributions at some point `c₀`; the "maximum-likelihood" adversary that
guesses whichever message makes `c` more likely then wins with probability
strictly better than `1/2`, so the scheme can't be perfectly
indistinguishable either. -/
theorem PerfectlyIndistinguishable.perfectSecrecy {S : EncScheme M K C}
    (hI : PerfectlyIndistinguishable S) : PerfectSecrecy S := by
  by_contra hns
  unfold PerfectSecrecy at hns
  simp only [not_forall] at hns
  obtain ⟨m₀, m₁, c₀, hne⟩ := hns
  set A : Adversary M C := ⟨(m₀, m₁), fun c => decide (ctDist S m₀ c ≤ ctDist S m₁ c)⟩ with hA
  have hsucc := hI A
  rw [privKeav_eq] at hsucc
  have hA2 : A.choose.2 = m₁ := rfl
  have hA1 : A.choose.1 = m₀ := rfl
  have hAguess : ∀ c, A.guess c = decide (ctDist S m₀ c ≤ ctDist S m₁ c) := fun _ => rfl
  simp only [hA1, hA2, hAguess, decide_eq_true_eq, mul_ite, mul_one, mul_zero] at hsucc
  rw [← ENNReal.tsum_add] at hsucc
  have hmax : ∀ c, (if ctDist S m₀ c ≤ ctDist S m₁ c then ctDist S m₁ c else 0) +
      (if ctDist S m₀ c ≤ ctDist S m₁ c then 0 else ctDist S m₀ c) =
      max (ctDist S m₀ c) (ctDist S m₁ c) := by
    intro c
    by_cases h : ctDist S m₀ c ≤ ctDist S m₁ c
    · simp [h]
    · simp [h, max_eq_left (not_le.mp h).le]
  rw [tsum_congr hmax] at hsucc
  have hgt : (1 : ENNReal) < ∑' c, max (ctDist S m₀ c) (ctDist S m₁ c) := by
    rcases lt_or_gt_of_ne hne with h | h
    · calc (1 : ENNReal) = ∑' c, ctDist S m₀ c := (PMF.tsum_coe _).symm
        _ < ∑' c, max (ctDist S m₀ c) (ctDist S m₁ c) :=
          ENNReal.tsum_lt_tsum (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
            (fun c => le_max_left _ _) (lt_of_lt_of_le h (le_max_right _ _))
    · calc (1 : ENNReal) = ∑' c, ctDist S m₁ c := (PMF.tsum_coe _).symm
        _ < ∑' c, max (ctDist S m₀ c) (ctDist S m₁ c) :=
          ENNReal.tsum_lt_tsum (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
            (fun c => le_max_right _ _) (lt_of_lt_of_le h (le_max_left _ _))
  have hfinal : 2⁻¹ * (1 : ENNReal) < 2⁻¹ * ∑' c, max (ctDist S m₀ c) (ctDist S m₁ c) :=
    ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hgt
  rw [mul_one, hsucc] at hfinal
  norm_num at hfinal

/-- **Exercise 2.6.** Perfect secrecy (Definition 2.3) and perfect
indistinguishability (Definition 2.6) are equivalent. -/
theorem perfectSecrecy_iff_perfectlyIndistinguishable (S : EncScheme M K C) :
    PerfectSecrecy S ↔ PerfectlyIndistinguishable S :=
  ⟨PerfectSecrecy.perfectlyIndistinguishable, PerfectlyIndistinguishable.perfectSecrecy⟩

end ExplainableCrypto.KatzLindell
