import ExplainableCrypto.Helios.Symbolic.MinimalRecipes
import ExplainableCrypto.Helios.Symbolic.ProjectionPaths

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- The complete size-one syntax class; names remain unbounded. -/
theorem Term.nodeCount_one_cases {t : Term V} (h : t.nodeCount ≤ 1) :
    (∃ n, t = .name n) ∨ (∃ v, t = .var v) ∨ (∃ c, t = .const c) := by
  cases t with
  | name n => exact Or.inl ⟨n, rfl⟩
  | var v => exact Or.inr (Or.inl ⟨v, rfl⟩)
  | const c => exact Or.inr (Or.inr ⟨c, rfl⟩)
  | unary f a => have := a.nodeCount_pos; simp only [Term.nodeCount] at h; omega
  | binary f a b => have := a.nodeCount_pos; simp only [Term.nodeCount] at h; omega
  | ternary f a b c => have := a.nodeCount_pos; simp only [Term.nodeCount] at h; omega
  | spk a b c d => have := a.nodeCount_pos; simp only [Term.nodeCount] at h; omega

/-- Size at most two permits only atoms and a unary operator on an atom. -/
theorem Term.nodeCount_two_cases {t : Term V} (h : t.nodeCount ≤ 2) :
    t.nodeCount ≤ 1 ∨ ∃ f a, t = .unary f a ∧ a.nodeCount ≤ 1 := by
  cases t with
  | name n => exact Or.inl (by simp [Term.nodeCount])
  | var v => exact Or.inl (by simp [Term.nodeCount])
  | const c => exact Or.inl (by simp [Term.nodeCount])
  | unary f a => exact Or.inr ⟨f, a, rfl, by simp only [Term.nodeCount] at h; omega⟩
  | binary f a b =>
    have := a.nodeCount_pos; have := b.nodeCount_pos
    simp only [Term.nodeCount] at h; omega
  | ternary f a b c =>
    have := a.nodeCount_pos; have := b.nodeCount_pos
    simp only [Term.nodeCount] at h; omega
  | spk a b c d =>
    have := a.nodeCount_pos; have := b.nodeCount_pos
    simp only [Term.nodeCount] at h; omega

/-- A normal argument with a non-pair head cannot reveal a pair by projection. -/
theorem projection_not_eqE_penc_of_irreducible {a k r m : Term V}
    (ha : Irreducible a) (hp : a.headTag ≠ .binary .pair) (f : Unary) :
    ¬ EqE (.unary f a) (.ternary .penc k r m) := by
  intro he
  cases f with
  | pk => exact pk_not_eqE_penc _ _ _ _ he
  | fst =>
    obtain ⟨x, y, hs, _⟩ := he.projection_penc_inversion (Or.inl rfl)
    exact hp (ha.reducesModulo hs).head_eq
  | snd =>
    obtain ⟨x, y, hs, _⟩ := he.projection_penc_inversion (Or.inr rfl)
    exact hp (ha.reducesModulo hs).head_eq

/-- With no ciphertext-valued handle, an atomic recipe cannot produce a ciphertext. -/
theorem ciphertext_recipe_size_ge_two (σ : V → Term W) (k r m : Term W)
    (hv : ∀ v, ¬ EqE (σ v) (.ternary .penc k r m))
    {t : Term V} (he : EqE (t.subst σ) (.ternary .penc k r m)) :
    2 ≤ t.nodeCount := by
  by_contra hn
  have hs : t.nodeCount ≤ 1 := by omega
  rcases Term.nodeCount_one_cases hs with ⟨n, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
  · obtain ⟨_, _, _, hh, _⟩ := he.symm.penc_irreducible_shape (name_irreducible n)
    cases hh
  · exact hv v he
  · obtain ⟨_, _, _, hh, _⟩ := he.symm.penc_irreducible_shape (constant_irreducible c)
    cases hh

/-- If handles and their immediate unary images miss a ciphertext, every recipe
for it needs at least three nodes. No bound is imposed on available names. -/
theorem ciphertext_recipe_size_ge_three (σ : V → Term W) (k r m : Term W)
    (hv : ∀ v, ¬ EqE (σ v) (.ternary .penc k r m))
    (hu : ∀ f v, ¬ EqE (.unary f (σ v)) (.ternary .penc k r m))
    {t : Term V} (he : EqE (t.subst σ) (.ternary .penc k r m)) :
    3 ≤ t.nodeCount := by
  by_contra hn
  have hs : t.nodeCount ≤ 2 := by omega
  rcases t.nodeCount_two_cases hs with ha | ⟨f, a, rfl, ha⟩
  · have := ciphertext_recipe_size_ge_two σ k r m hv he
    omega
  · rcases Term.nodeCount_one_cases ha with ⟨n, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
    · exact projection_not_eqE_penc_of_irreducible (name_irreducible n) (by simp [Term.headTag]) f he
    · exact hu f v he
    · exact projection_not_eqE_penc_of_irreducible (constant_irreducible c) (by cases c <;> simp [Term.headTag]) f he

end ExplainableCrypto.Helios.Symbolic
