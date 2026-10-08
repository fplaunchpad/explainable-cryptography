import ExplainableCrypto.Helios.Symbolic.ProjectionPaths
import ExplainableCrypto.Helios.Symbolic.DecryptionPaths

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem projection_normal_shape_of_no_pair (f : Unary) (hf : f = .fst ∨ f = .snd)
    (a : Term V) (hn : ∀ x y, ¬ EqE a (.binary .pair x y)) {t : Term V}
    (ht : Irreducible t) (he : EqE (.unary f a) t) :
    ∃ a', t = .unary f a' ∧ EqE a a' := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  rcases hl.projection_cases hf with ⟨a₁, ha, hw⟩ | ⟨x, y, hp, _⟩
  · obtain ⟨a₂, ht₂, ha₂⟩ := ((ht.reducesModulo hr).trans hw).symm.unary_shape
    exact ⟨a₂, ht₂, ha.sound.trans ha₂.sound⟩
  · exact False.elim (hn x y hp.sound)

theorem projection_normal_form_of_no_pair (f : Unary) (hf : f = .fst ∨ f = .snd)
    (a : Term V) (hn : ∀ x y, ¬ EqE a (.binary .pair x y)) {a' t : Term V}
    (ha : Irreducible a') (ht : Irreducible t) (hea : EqE a a')
    (he : EqE (.unary f a) t) : BaseEq t (.unary f a') := by
  obtain ⟨a₁, rfl, h₁⟩ := projection_normal_shape_of_no_pair f hf a hn ht he
  have ha₁ := ht.context_hole (.unary f .hole)
  exact .unary f ((irreducible_eqE_iff_base ha₁ ha).mp (h₁.symm.trans hea))

end ExplainableCrypto.Helios.Symbolic
