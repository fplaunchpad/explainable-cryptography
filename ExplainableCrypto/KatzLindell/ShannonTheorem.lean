import ExplainableCrypto.KatzLindell.PerfectSecrecy

/-!
# Theorem 2.12 (Shannon's theorem)

A formalization of Theorem 2.12 from Katz and Lindell, *Introduction to
Modern Cryptography*: when `|M| = |K| = |C|`, a correct scheme is perfectly
secret iff keys are chosen uniformly and, for every message/ciphertext pair,
exactly one key could have produced that ciphertext from that message.

The book's proof assumes `Enc` is WLOG deterministic; here that fact is
*derived* (not assumed) from `Correct` together with the cardinality
hypothesis, via a pigeonhole argument on `PMF.support`.
-/

namespace ExplainableCrypto.KatzLindell

variable {M K C : Type}

/-- Condition 1 of Theorem 2.12: every key is chosen with the same
probability `1 / |K|`. -/
def UniformKeygen (S : EncScheme M K C) [Fintype K] : Prop :=
  ∀ k, S.keygen k = (Fintype.card K : ENNReal)⁻¹

/-- Condition 2 of Theorem 2.12: for every message and ciphertext, exactly
one key could have produced that ciphertext from that message. -/
def UniqueKeyPerCiphertext (S : EncScheme M K C) : Prop :=
  ∀ m c, ∃! k, c ∈ (S.encrypt k m).support

section Pigeonhole

/-- If `ι`-many pairwise disjoint nonempty finsets of `α` have `|ι| = |α|`,
every one of them is a singleton, and together they cover all of `α`. -/
private theorem pairwise_disjoint_card_eq_one_and_cover
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] {t : ι → Finset α}
    (hdisj : Pairwise fun i j => Disjoint (t i) (t j))
    (hne : ∀ i, (t i).Nonempty) (hcard : Fintype.card ι = Fintype.card α) :
    (∀ i, (t i).card = 1) ∧ Finset.univ.biUnion t = Finset.univ := by
  classical
  have hbiUnion : (Finset.univ.biUnion t).card = ∑ j, (t j).card :=
    Finset.card_biUnion (hdisj.set_pairwise _)
  have hle : ∑ j, (t j).card ≤ Fintype.card α := by
    rw [← hbiUnion]
    calc (Finset.univ.biUnion t).card ≤ (Finset.univ : Finset α).card := Finset.card_le_univ _
      _ = Fintype.card α := Finset.card_univ
  have hge : Fintype.card α ≤ ∑ j, (t j).card := by
    rw [← hcard]
    calc Fintype.card ι = ∑ _j : ι, 1 := by simp
      _ ≤ ∑ j, (t j).card := by
          apply Finset.sum_le_sum
          intro j _
          have := Finset.card_pos.mpr (hne j); omega
  have hsum : ∑ j, (t j).card = Fintype.card α := le_antisymm hle hge
  have hone : ∀ i, (t i).card = 1 := by
    intro i
    by_contra hne1
    have hpos : 0 < (t i).card := Finset.card_pos.mpr (hne i)
    have hgt : Fintype.card α < ∑ j, (t j).card := by
      rw [← hcard]
      calc Fintype.card ι = ∑ _j : ι, 1 := by simp
        _ < ∑ j, (t j).card := by
            apply Finset.sum_lt_sum
            · intro j _
              have := Finset.card_pos.mpr (hne j); omega
            · exact ⟨i, Finset.mem_univ i, by omega⟩
    omega
  refine ⟨hone, ?_⟩
  apply Finset.eq_univ_of_card
  rw [hbiUnion]
  exact hsum

end Pigeonhole

variable [Fintype M] [Fintype K] [Fintype C] [DecidableEq C]

omit [DecidableEq C] in
/-- From a singleton support `{c}`, the whole probability mass sits at `c`. -/
private theorem eq_one_and_rest_zero_of_singleton_support {p : PMF C} {c : C}
    (h : Finset.univ.filter (fun c' => p c' ≠ 0) = {c}) :
    p c = 1 ∧ ∀ c', c' ≠ c → p c' = 0 := by
  classical
  have hzero : ∀ c', c' ≠ c → p c' = 0 := by
    intro c' hc'
    by_contra hne
    have hmem : c' ∈ Finset.univ.filter (fun c'' => p c'' ≠ 0) := by simp [hne]
    rw [h] at hmem
    exact hc' (Finset.mem_singleton.mp hmem)
  refine ⟨?_, hzero⟩
  have hsum : ∑' c', p c' = p c := tsum_eq_single c (fun c' hc' => hzero c' hc')
  rw [← hsum, PMF.tsum_coe]

omit [Fintype M] [Fintype K] [DecidableEq C] in
/-- A convenience form: given that the support is a singleton, the value at
any particular point of that support is `1`. -/
private theorem eq_one_of_mem_support_of_card_eq_one {S : EncScheme M K C} {k : K} {m : M}
    {c : C} (hcard1 : (Finset.univ.filter (fun c' => S.encrypt k m c' ≠ 0)).card = 1)
    (hc : c ∈ (S.encrypt k m).support) : S.encrypt k m c = 1 := by
  classical
  obtain ⟨c', hc'⟩ := Finset.card_eq_one.mp hcard1
  have hmem : c ∈ Finset.univ.filter (fun c'' => S.encrypt k m c'' ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c, ((S.encrypt k m).mem_support_iff c).mp hc⟩
  rw [hc'] at hmem
  rw [Finset.mem_singleton.mp hmem]
  exact (eq_one_and_rest_zero_of_singleton_support hc').1

omit [Fintype M] [Fintype K] [DecidableEq C] in
private theorem encrypt_support_filter_nonempty (S : EncScheme M K C) (k : K) (m : M) :
    (Finset.univ.filter (fun c => S.encrypt k m c ≠ 0)).Nonempty := by
  classical
  obtain ⟨c, hc⟩ := (S.encrypt k m).support_nonempty
  exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, ((S.encrypt k m).mem_support_iff c).mp hc⟩⟩

omit [Fintype M] [Fintype K] [DecidableEq C] in
/-- For a *live* key under a correct scheme, encryptions of distinct
messages can never land on the same ciphertext (else decryption would be
ambiguous). -/
private theorem Correct.encrypt_pairwise_disjoint {S : EncScheme M K C} (hCorrect : Correct S)
    {k : K} (hk : k ∈ S.keygen.support) :
    Pairwise fun m₁ m₂ => Disjoint
      (Finset.univ.filter (fun c => S.encrypt k m₁ c ≠ 0))
      (Finset.univ.filter (fun c => S.encrypt k m₂ c ≠ 0)) := by
  classical
  intro m₁ m₂ hm
  rw [Finset.disjoint_left]
  intro c hc₁ hc₂
  have h1 : S.decrypt k c = m₁ :=
    hCorrect k hk m₁ c (((S.encrypt k m₁).mem_support_iff c).mpr (Finset.mem_filter.mp hc₁).2)
  have h2 : S.decrypt k c = m₂ :=
    hCorrect k hk m₂ c (((S.encrypt k m₂).mem_support_iff c).mpr (Finset.mem_filter.mp hc₂).2)
  exact hm (h1.symm.trans h2)

omit [Fintype K] in
/-- The key structural fact behind the forward direction: for a live key `k`
under a correct scheme with `|M| = |C|`, encryption is deterministic for
every message. This is exactly the WLOG claim the book's proof assumes. -/
private theorem Correct.singleton_support_of_card_eq {S : EncScheme M K C}
    (hCorrect : Correct S) (hMC : Fintype.card M = Fintype.card C)
    {k : K} (hk : k ∈ S.keygen.support) (m : M) :
    (Finset.univ.filter (fun c => S.encrypt k m c ≠ 0)).card = 1 :=
  (pairwise_disjoint_card_eq_one_and_cover (Correct.encrypt_pairwise_disjoint hCorrect hk)
    (fun m' => encrypt_support_filter_nonempty S k m') hMC).1 m

omit [Fintype M] [Fintype K] [DecidableEq C] in
/-- For a fixed message, distinct keys satisfying the uniqueness condition
can never both produce the same ciphertext. -/
private theorem UniqueKeyPerCiphertext.encrypt_pairwise_disjoint {S : EncScheme M K C}
    (hUniq : UniqueKeyPerCiphertext S) (m : M) :
    Pairwise fun k₁ k₂ => Disjoint
      (Finset.univ.filter (fun c => S.encrypt k₁ m c ≠ 0))
      (Finset.univ.filter (fun c => S.encrypt k₂ m c ≠ 0)) := by
  classical
  intro k₁ k₂ hk
  rw [Finset.disjoint_left]
  intro c hc₁ hc₂
  obtain ⟨k', -, hk'⟩ := hUniq m c
  have e1 : k₁ = k' :=
    hk' k₁ (((S.encrypt k₁ m).mem_support_iff c).mpr (Finset.mem_filter.mp hc₁).2)
  have e2 : k₂ = k' :=
    hk' k₂ (((S.encrypt k₂ m).mem_support_iff c).mpr (Finset.mem_filter.mp hc₂).2)
  exact hk (e1.trans e2.symm)

omit [Fintype M] in
/-- The key structural fact behind the backward direction: condition 2
together with `|K| = |C|` forces encryption to be deterministic too — with
no `Correct` hypothesis needed at all. -/
private theorem UniqueKeyPerCiphertext.singleton_of_card_eq {S : EncScheme M K C}
    (hUniq : UniqueKeyPerCiphertext S) (hKC : Fintype.card K = Fintype.card C) (m : M) (k : K) :
    (Finset.univ.filter (fun c => S.encrypt k m c ≠ 0)).card = 1 :=
  (pairwise_disjoint_card_eq_one_and_cover (UniqueKeyPerCiphertext.encrypt_pairwise_disjoint hUniq m)
    (fun k' => encrypt_support_filter_nonempty S k' m) hKC).1 k

/-- If `f ≤ c` pointwise and `∑ f` is exactly `|ι| • c`, every value of `f`
equals `c`. The ENNReal analogue of the natural-number pigeonhole bound
above, proved via `ENNReal.tsum_lt_tsum` since ENNReal is not cancellative
(so the usual `Finset.sum_lt_sum` doesn't apply). -/
private theorem eq_of_le_of_sum_eq_card_mul {ι : Type*} [Fintype ι] {f : ι → ENNReal} {c : ENNReal}
    (hc_ne_top : c ≠ ⊤) (hle : ∀ i, f i ≤ c) (hsum : ∑ i, f i = (Fintype.card ι : ENNReal) * c)
    (i : ι) : f i = c := by
  by_contra hne
  have hlt : f i < c := lt_of_le_of_ne (hle i) hne
  have hconst : ∑ _j : ι, c = (Fintype.card ι : ENNReal) * c := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hftop : (∑' j, f j) ≠ ⊤ := by
    simp only [tsum_fintype]
    rw [hsum]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hc_ne_top
  have hstrict : ∑' j, f j < ∑' _j : ι, c := ENNReal.tsum_lt_tsum hftop hle hlt
  simp only [tsum_fintype] at hstrict
  rw [hsum, hconst] at hstrict
  exact lt_irrefl _ hstrict

omit [Fintype K] in
/-- For a fixed live key `k` and ciphertext `c₀`, summing the (singleton)
ciphertext probability over all messages gives exactly `1`: every ciphertext
is reached from exactly one message under this key. -/
private theorem sum_encrypt_eq_one_of_pairwise_disjoint {S : EncScheme M K C} {k : K}
    (hdisj : Pairwise fun m₁ m₂ => Disjoint
      (Finset.univ.filter (fun c => S.encrypt k m₁ c ≠ 0))
      (Finset.univ.filter (fun c => S.encrypt k m₂ c ≠ 0)))
    (hne : ∀ m, (Finset.univ.filter (fun c => S.encrypt k m c ≠ 0)).Nonempty)
    (hMC : Fintype.card M = Fintype.card C) (c₀ : C) :
    ∑ m, S.encrypt k m c₀ = 1 := by
  classical
  obtain ⟨hdet, hcov⟩ := pairwise_disjoint_card_eq_one_and_cover hdisj hne hMC
  obtain ⟨m₀, hm₀⟩ : ∃ m, S.encrypt k m c₀ ≠ 0 := by
    have hc₀mem : c₀ ∈ Finset.univ.biUnion
        (fun m => Finset.univ.filter (fun c => S.encrypt k m c ≠ 0)) := by
      rw [hcov]; exact Finset.mem_univ c₀
    obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.mp hc₀mem
    exact ⟨m, (Finset.mem_filter.mp hm).2⟩
  have hmem₀ : c₀ ∈ Finset.univ.filter (fun c => S.encrypt k m₀ c ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ c₀, hm₀⟩
  have hval : S.encrypt k m₀ c₀ = 1 :=
    eq_one_of_mem_support_of_card_eq_one (hdet m₀) (((S.encrypt k m₀).mem_support_iff c₀).mpr hm₀)
  rw [← hval]
  apply Finset.sum_eq_single
  · intro m' _ hm'
    by_contra hne'
    have hmem' : c₀ ∈ Finset.univ.filter (fun c => S.encrypt k m' c ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ c₀, hne'⟩
    exact (Finset.disjoint_left.mp (hdisj hm') hmem') hmem₀
  · intro h; exact absurd (Finset.mem_univ m₀) h

/-- **Theorem 2.12 (Shannon's theorem).** When `|M| = |K| = |C|`, a correct
scheme is perfectly secret iff keys are uniform and every message/ciphertext
pair has a unique witnessing key. -/
theorem perfectSecrecy_iff_shannon
    (hMK : Fintype.card M = Fintype.card K) (hKC : Fintype.card K = Fintype.card C)
    {S : EncScheme M K C} (hCorrect : Correct S) :
    PerfectSecrecy S ↔ UniformKeygen S ∧ UniqueKeyPerCiphertext S := by
  classical
  have hMC : Fintype.card M = Fintype.card C := hMK.trans hKC
  constructor
  · -- forward direction
    intro hSecret
    obtain ⟨k₁, hk₁⟩ := S.keygen.support_nonempty
    have hKpos : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨k₁⟩
    have hMpos : 0 < Fintype.card M := by rw [hMK]; exact hKpos
    obtain ⟨m₁⟩ : Nonempty M := Fintype.card_pos_iff.mp hMpos
    have hMne0 : (Fintype.card M : ENNReal) ≠ 0 := by exact_mod_cast hMpos.ne'
    have hMnetop : (Fintype.card M : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- Step A: the ciphertext distribution is uniform, equal to `(card M)⁻¹`.
    have hstepA : ∀ k, k ∈ S.keygen.support → ∀ c, ∑ m, S.encrypt k m c = 1 := fun k hk c =>
      sum_encrypt_eq_one_of_pairwise_disjoint (Correct.encrypt_pairwise_disjoint hCorrect hk)
        (fun m => encrypt_support_filter_nonempty S k m) hMC c
    have hCtUniform : ∀ c m, ctDist S m c = (Fintype.card M : ENNReal)⁻¹ := by
      intro c
      have hsum_ct1 : ∑ m, ctDist S m c = 1 := by
        have hunfold : ∀ m, ctDist S m c = ∑ k, S.keygen k * S.encrypt k m c := by
          intro m; simp only [ctDist, PMF.bind_apply, tsum_fintype]
        simp only [hunfold]
        rw [Finset.sum_comm]
        have hinner : ∀ k, ∑ m, S.keygen k * S.encrypt k m c = S.keygen k := by
          intro k
          by_cases hk0 : S.keygen k = 0
          · simp [hk0]
          · rw [← Finset.mul_sum, hstepA k ((S.keygen.mem_support_iff k).mpr hk0), mul_one]
        simp only [hinner]
        have hcoe := PMF.tsum_coe S.keygen
        rwa [tsum_fintype] at hcoe
      have hsum_ct : ∑ m, ctDist S m c = (Fintype.card M : ENNReal) * ctDist S m₁ c := by
        rw [Finset.sum_congr rfl (fun m _ => hSecret m m₁ c), Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      have heq : (Fintype.card M : ENNReal) * ctDist S m₁ c = 1 := hsum_ct.symm.trans hsum_ct1
      have hval1 : ctDist S m₁ c = (Fintype.card M : ENNReal)⁻¹ := by
        have h2 : (Fintype.card M : ENNReal)⁻¹ * ((Fintype.card M : ENNReal) * ctDist S m₁ c) =
            (Fintype.card M : ENNReal)⁻¹ * 1 := by rw [heq]
        rwa [← mul_assoc, ENNReal.inv_mul_cancel hMne0 hMnetop, one_mul, mul_one] at h2
      intro m
      rw [hSecret m m₁ c]
      exact hval1
    -- Step B: every key gets probability at most `(card M)⁻¹` — and, by a
    -- counting argument over all of `K`, exactly `(card M)⁻¹`.
    have hStepB_bound : ∀ k, S.keygen k ≤ (Fintype.card M : ENNReal)⁻¹ := by
      intro k
      by_cases hk : k ∈ S.keygen.support
      · obtain ⟨c, hc⟩ := (S.encrypt k m₁).support_nonempty
        have hdet1 := Correct.singleton_support_of_card_eq hCorrect hMC hk m₁
        have hval1 : S.encrypt k m₁ c = 1 := eq_one_of_mem_support_of_card_eq_one hdet1 hc
        have hle : S.keygen k * S.encrypt k m₁ c ≤ ctDist S m₁ c := by
          have heqsum : ctDist S m₁ c = ∑ k', S.keygen k' * S.encrypt k' m₁ c := by
            simp only [ctDist, PMF.bind_apply, tsum_fintype]
          rw [heqsum]
          exact Finset.single_le_sum (fun k' _ => (zero_le : (0 : ENNReal) ≤ _)) (Finset.mem_univ k)
        rw [hval1, mul_one, hCtUniform c m₁] at hle
        exact hle
      · have hz : S.keygen k = 0 := by
          by_contra h; exact hk ((S.keygen.mem_support_iff k).mpr h)
        rw [hz]; exact zero_le
    have hsum_keygen : ∑ k, S.keygen k = 1 := by
      have hcoe := PMF.tsum_coe S.keygen
      rwa [tsum_fintype] at hcoe
    have hRHS : (Fintype.card K : ENNReal) * (Fintype.card M : ENNReal)⁻¹ = 1 := by
      rw [← hMK, mul_comm]
      exact ENNReal.inv_mul_cancel hMne0 hMnetop
    have hUniform_eq : ∀ k, S.keygen k = (Fintype.card M : ENNReal)⁻¹ :=
      eq_of_le_of_sum_eq_card_mul (ENNReal.inv_ne_top.mpr hMne0) hStepB_bound
        (hsum_keygen.trans hRHS.symm)
    have hUniform : UniformKeygen S := by
      intro k; rw [hUniform_eq k, hMK]
    have hlive : ∀ k, k ∈ S.keygen.support := fun k =>
      (S.keygen.mem_support_iff k).mpr
        (by rw [hUniform_eq k]; exact ENNReal.inv_ne_zero.mpr hMnetop)
    -- Step C: for every `(m, c)`, exactly one key witnesses it.
    have hUniq : UniqueKeyPerCiphertext S := by
      intro m c
      have hbool : ∀ k, S.encrypt k m c = 0 ∨ S.encrypt k m c = 1 := by
        intro k
        by_cases hmem : c ∈ (S.encrypt k m).support
        · right
          exact eq_one_of_mem_support_of_card_eq_one
            (Correct.singleton_support_of_card_eq hCorrect hMC (hlive k) m) hmem
        · left
          exact not_not.mp (fun h => hmem ((S.encrypt k m).mem_support_iff c |>.mpr h))
      have hsum1 : ∑ k, S.encrypt k m c = 1 := by
        have h1 : ctDist S m c = (Fintype.card K : ENNReal)⁻¹ := by rw [hCtUniform c m, hMK]
        have h2 : ctDist S m c = ∑ k, S.keygen k * S.encrypt k m c := by
          simp only [ctDist, PMF.bind_apply, tsum_fintype]
        have h3 : ∑ k, S.keygen k * S.encrypt k m c =
            (Fintype.card K : ENNReal)⁻¹ * ∑ k, S.encrypt k m c := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by rw [hUniform_eq k, hMK])
        have h4 : (Fintype.card K : ENNReal)⁻¹ * ∑ k, S.encrypt k m c =
            (Fintype.card K : ENNReal)⁻¹ := by rw [← h3, ← h2, h1]
        have hKne0 : (Fintype.card K : ENNReal) ≠ 0 := by rw [← hMK]; exact hMne0
        have hKnetop : (Fintype.card K : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
        have h5 := congrArg (fun x => (Fintype.card K : ENNReal) * x) h4
        simpa [← mul_assoc, ENNReal.mul_inv_cancel hKne0 hKnetop] using h5
      obtain ⟨k₀, hk₀⟩ : ∃ k, S.encrypt k m c = 1 := by
        by_contra hnone
        push Not at hnone
        have hallzero' : ∀ k, S.encrypt k m c = 0 := fun k => (hbool k).resolve_right (hnone k)
        rw [Finset.sum_eq_zero (fun k _ => hallzero' k)] at hsum1
        exact zero_ne_one hsum1
      have hsplit : S.encrypt k₀ m c + ∑ k ∈ Finset.univ.erase k₀, S.encrypt k m c = 1 := by
        rw [Finset.add_sum_erase Finset.univ (fun k => S.encrypt k m c) (Finset.mem_univ k₀)]
        exact hsum1
      rw [hk₀] at hsplit
      have heq2 : (1 : ENNReal) + ∑ k ∈ Finset.univ.erase k₀, S.encrypt k m c = 1 + 0 := by
        rw [add_zero]; exact hsplit
      have hrest0 : ∑ k ∈ Finset.univ.erase k₀, S.encrypt k m c = 0 :=
        (ENNReal.add_right_inj ENNReal.one_ne_top).mp heq2
      have hallzero : ∀ k ∈ Finset.univ.erase k₀, S.encrypt k m c = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => (zero_le : (0 : ENNReal) ≤ _))).mp hrest0
      refine ⟨k₀, ((S.encrypt k₀ m).mem_support_iff c).mpr (by rw [hk₀]; exact one_ne_zero), ?_⟩
      intro k hkmem
      by_contra hne
      exact ((S.encrypt k m).mem_support_iff c).mp hkmem
        (hallzero k (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩))
    exact ⟨hUniform, hUniq⟩
  · -- backward direction
    rintro ⟨hUniform, hUniq⟩ m₀ m₁ c
    have hval : ∀ m, ctDist S m c = (Fintype.card K : ENNReal)⁻¹ := by
      intro m
      obtain ⟨k₀, hk₀mem, hk₀uniq⟩ := hUniq m c
      have hdet := UniqueKeyPerCiphertext.singleton_of_card_eq hUniq hKC m k₀
      have hval₀ : S.encrypt k₀ m c = 1 := eq_one_of_mem_support_of_card_eq_one hdet hk₀mem
      have hzero : ∀ k, k ≠ k₀ → S.encrypt k m c = 0 := by
        intro k hk
        by_contra hc
        exact hk (hk₀uniq k (((S.encrypt k m).mem_support_iff c).mpr hc))
      calc ctDist S m c = ∑ k, S.keygen k * S.encrypt k m c := by
            simp only [ctDist, PMF.bind_apply, tsum_fintype]
        _ = S.keygen k₀ * S.encrypt k₀ m c := by
            apply Finset.sum_eq_single
            · intro k _ hk
              rw [hzero k hk, mul_zero]
            · intro h; exact absurd (Finset.mem_univ k₀) h
        _ = (Fintype.card K : ENNReal)⁻¹ := by rw [hval₀, mul_one, hUniform k₀]
    rw [hval m₀, hval m₁]

end ExplainableCrypto.KatzLindell
