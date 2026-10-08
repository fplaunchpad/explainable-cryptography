import ExplainableCrypto.Helios.Symbolic.OuterFusion
import ExplainableCrypto.Helios.Symbolic.ReductionSubstitution

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- No oriented rule has a ciphertext constructor at its source root. -/
theorem RootStep.not_penc {k r m t : Term V} :
    ¬ RootStep (.ternary .penc k r m) t := by
  intro h
  cases h

/-- A raw contextual step from a ciphertext changes exactly one argument. -/
theorem RewriteStep.penc_cases {k r m t : Term V}
    (h : RewriteStep (.ternary .penc k r m) t) :
    (∃ k', RewriteStep k k' ∧ t = .ternary .penc k' r m) ∨
    (∃ r', RewriteStep r r' ∧ t = .ternary .penc k r' m) ∨
    (∃ m', RewriteStep m m' ∧ t = .ternary .penc k r m') := by
  obtain ⟨c, l, u, hr, hs, rfl⟩ := h
  cases c with
  | hole =>
    simp only [Context.fill] at hs
    subst l
    exact False.elim (RootStep.not_penc hr)
  | ternaryFirst f c b d =>
    simp only [Context.fill, Term.ternary.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inl ⟨c.fill u, ⟨c, l, u, hr, rfl, rfl⟩, rfl⟩
  | ternarySecond f a c d =>
    simp only [Context.fill, Term.ternary.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inl ⟨c.fill u, ⟨c, l, u, hr, rfl, rfl⟩, rfl⟩)
  | ternaryThird f a b c =>
    simp only [Context.fill, Term.ternary.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    exact Or.inr (Or.inr ⟨c.fill u, ⟨c, l, u, hr, rfl, rfl⟩, rfl⟩)
  | _ => cases hs

/-- E0 representatives do not add a fourth ciphertext-step case. The unchanged
arguments are the original terms; the target equality absorbs their E0 changes. -/
theorem ModuloStep.penc_cases {k r m t : Term V}
    (h : ModuloStep (.ternary .penc k r m) t) :
    (∃ k', ModuloStep k k' ∧ BaseEq t (.ternary .penc k' r m)) ∨
    (∃ r', ModuloStep r r' ∧ BaseEq t (.ternary .penc k r' m)) ∨
    (∃ m', ModuloStep m m' ∧ BaseEq t (.ternary .penc k r m')) := by
  obtain ⟨a, b, ha, hr, hb⟩ := h
  obtain ⟨k₀, r₀, m₀, rfl, hk, hrr, hm⟩ := ha.penc_shape
  rcases hr.penc_cases with ⟨k', h, rfl⟩ | ⟨r', h, rfl⟩ | ⟨m', h, rfl⟩
  · exact Or.inl ⟨k', ⟨k₀, k', hk, h, .refl _⟩,
      hb.symm.trans (.ternary .penc (.refl _) hrr.symm hm.symm)⟩
  · exact Or.inr (Or.inl ⟨r', ⟨r₀, r', hrr, h, .refl _⟩,
      hb.symm.trans (.ternary .penc hk.symm (.refl _) hm.symm)⟩)
  · exact Or.inr (Or.inr ⟨m', ⟨m₀, m', hm, h, .refl _⟩,
      hb.symm.trans (.ternary .penc hk.symm hrr.symm (.refl _))⟩)

/-- Fusion versus any modulo step inside its first ciphertext. Key changes
synchronize the second key copy before fusing; other components commute. -/
theorem fusion_ciphertext_peak_joined (k r s m n : Term V) {t : Term V}
    (ht : ModuloStep (.ternary .penc k r m) t) :
    JoinModulo (combinedCiphertext k r s m n)
      (.binary .mul t (.ternary .penc k s n)) := by
  rcases ht.penc_cases with ⟨k', hk, he⟩ | ⟨r', hr, he⟩ | ⟨m', hm, he⟩
  · refine ⟨combinedCiphertext k' r s m n, ?_, ?_⟩
    · exact .single (hk.context (.ternaryFirst .penc .hole
        (.binary .compose r s) (.binary .add m n)))
    · exact ((ReducesModulo.single (hk.context
        (.binaryRight .mul (.ternary .penc k' r m)
          (.ternaryFirst .penc .hole s n)))).trans
        (.single (RootStep.homomorphic k' r s m n).to_modulo)).pre_base
          (.binary .mul he (.refl _))
  · refine ⟨combinedCiphertext k r' s m n, ?_, ?_⟩
    · exact .single (hr.context (.ternarySecond .penc k
        (.binaryLeft .compose .hole s) (.binary .add m n)))
    · exact .single ((RootStep.homomorphic k r' s m n).to_modulo.pre_base
        (.binary .mul he (.refl _)))
  · refine ⟨combinedCiphertext k r s m' n, ?_, ?_⟩
    · exact .single (hm.context (.ternaryThird .penc k
        (.binary .compose r s) (.binaryLeft .add .hole n)))
    · exact .single ((RootStep.homomorphic k r s m' n).to_modulo.pre_base
        (.binary .mul he (.refl _)))

end ExplainableCrypto.Helios.Symbolic
