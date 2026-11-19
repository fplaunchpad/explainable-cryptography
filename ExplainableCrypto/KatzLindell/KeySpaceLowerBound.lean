import ExplainableCrypto.KatzLindell.PerfectSecrecy

/-!
# Theorem 2.11: perfect secrecy forces `|K| ≥ |M|`

A formalization of Theorem 2.11 from Katz and Lindell, *Introduction to
Modern Cryptography*: any correct, perfectly secret encryption scheme has
a key space at least as large as its message space.
-/

namespace ExplainableCrypto.KatzLindell

variable {M K C : Type}

/-- **Theorem 2.11.** If `S` is correct and perfectly secret, its key space
is at least as large as its message space.

Proof sketch: suppose `|K| < |M|`. Fix any `c₀` that some key `k₀` with
nonzero probability actually produces when encrypting some `m₀`. The set of
messages `decoded` that *some* key could decrypt `c₀` to has size at most
`|K| < |M|`, so some `m₁` is missed entirely: no key decrypts `c₀` to `m₁`.
By correctness, that means no key can encrypt `m₁` to `c₀` either, so
`ctDist S m₁ c₀ = 0` — but `ctDist S m₀ c₀ ≠ 0`, contradicting perfect
secrecy. -/
theorem Correct.card_message_le_card_key [Fintype M] [Fintype K]
    {S : EncScheme M K C} (hCorrect : Correct S) (hSecret : PerfectSecrecy S) :
    Fintype.card M ≤ Fintype.card K := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨m₀⟩ : Nonempty M := Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hlt)
  obtain ⟨k₀, hk₀⟩ := S.keygen.support_nonempty
  obtain ⟨c₀, hc₀⟩ := (S.encrypt k₀ m₀).support_nonempty
  -- the messages some key (live or not) could decrypt `c₀` to
  set decoded : Finset M := Finset.univ.image (fun k => S.decrypt k c₀) with hdecoded
  have hcard : decoded.card ≤ Fintype.card K :=
    le_trans Finset.card_image_le (le_of_eq Finset.card_univ)
  -- `decoded` is too small to cover all of `M`
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, m₁ ∉ decoded := by
    by_contra hall
    push Not at hall
    have : decoded = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ] at hcard
    exact absurd hcard (not_le.mpr hlt)
  have hm₁' : ∀ k : K, S.decrypt k c₀ ≠ m₁ := by
    intro k heq
    apply hm₁
    rw [hdecoded]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, heq⟩
  -- no key can encrypt `m₁` to `c₀`, so its ciphertext distribution there is `0`
  have hzero : ctDist S m₁ c₀ = 0 := by
    have hterm : ∀ k, S.keygen k * S.encrypt k m₁ c₀ = 0 := by
      intro k
      by_cases hk : S.keygen k = 0
      · simp [hk]
      · have henc : S.encrypt k m₁ c₀ = 0 := by
          by_contra hc
          exact hm₁' k (hCorrect k ((S.keygen.mem_support_iff k).mpr hk) m₁ c₀
            (((S.encrypt k m₁).mem_support_iff c₀).mpr hc))
        simp [henc]
    simp only [ctDist, PMF.bind_apply, ENNReal.tsum_eq_zero.mpr hterm]
  -- but `k₀` does encrypt `m₀` to `c₀` with nonzero probability
  have hpos : ctDist S m₀ c₀ ≠ 0 := by
    intro h
    simp only [ctDist, PMF.bind_apply] at h
    rw [ENNReal.tsum_eq_zero] at h
    exact mul_ne_zero ((S.keygen.mem_support_iff k₀).mp hk₀)
      (((S.encrypt k₀ m₀).mem_support_iff c₀).mp hc₀) (h k₀)
  exact hpos ((hSecret m₀ m₁ c₀).trans hzero)

end ExplainableCrypto.KatzLindell
