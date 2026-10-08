import ExplainableCrypto.Helios.Symbolic.StuckCheckOrigins
import ExplainableCrypto.Helios.Symbolic.ProjectionNormalForms

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Stuck projections preserve the selector as well as the argument under full
E. The no-pair conditions concern semantic values, not failed raw matching. -/
theorem EqE.projection_iff_of_no_pair (f g : Unary) (hf : f = .fst ∨ f = .snd)
    (hg : g = .fst ∨ g = .snd) (a b : Term V)
    (ha : ∀ x y, ¬ EqE a (.binary .pair x y))
    (hb : ∀ x y, ¬ EqE b (.binary .pair x y)) :
    EqE (.unary f a) (.unary g b) ↔ f = g ∧ EqE a b := by
  constructor
  · intro he
    obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
    rcases hl.projection_cases hf with ⟨a', ha', hw⟩ | ⟨x, y, hp, _⟩
    · rcases hr.projection_cases hg with ⟨b', hb', hw'⟩ | ⟨x, y, hp, _⟩
      · have hc := (BaseEq.unary_iff _ _ _ _).mp (hw.symm.trans hw')
        exact ⟨hc.1, ha'.sound.trans (hc.2.sound.trans hb'.sound.symm)⟩
      · exact False.elim (hb x y hp.sound)
    · exact False.elim (ha x y hp.sound)
  · rintro ⟨rfl, he⟩
    exact .unary _ he

/-- Stuck decryption retains both ordered arguments. Successful E5/E6 results
are outside this injectivity theorem. -/
theorem EqE.decryption_iff_of_no_match (a b c d : Term V)
    (hl : ∀ m, ¬ DecryptionMatch a b m) (hr : ∀ m, ¬ DecryptionMatch c d m) :
    EqE (.binary .dec a b) (.binary .dec c d) ↔ EqE a c ∧ EqE b d := by
  constructor
  · intro he
    obtain ⟨w, hleft, hright⟩ := (eqE_iff_join _ _).mp he
    rcases hleft.decryption_cases with ⟨a', b', ha, hb, hw⟩ | ⟨m, hm, _⟩
    · rcases hright.decryption_cases with ⟨c', d', hc, hd, hw'⟩ | ⟨m, hm, _⟩
      · have hh := ((BaseEq.binary_iff .dec .dec (by simp [AC]) (by simp [AC]) _ _ _ _).mp
          (hw.symm.trans hw')).2
        exact ⟨ha.sound.trans (hh.1.sound.trans hc.sound.symm),
          hb.sound.trans (hh.2.sound.trans hd.sound.symm)⟩
      · exact False.elim (hr m hm)
    · exact False.elim (hl m hm)
  · rintro ⟨ha, hb⟩
    exact .binary .dec ha hb

/-- Two different stuck destructor heads cannot become equal by reducing their
arguments. Both semantic no-match conditions remain explicit. -/
theorem stuck_projection_not_eqE_decryption (f : Unary) (hf : f = .fst ∨ f = .snd)
    (a b c : Term V) (ha : ∀ x y, ¬ EqE a (.binary .pair x y))
    (hd : ∀ m, ¬ DecryptionMatch b c m) :
    ¬ EqE (.unary f a) (.binary .dec b c) := by
  intro he
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  rcases hl.projection_cases hf with ⟨_, _, hw⟩ | ⟨x, y, hp, _⟩
  · rcases hr.decryption_cases with ⟨_, _, _, _, hw'⟩ | ⟨m, hm, _⟩
    · cases (hw.symm.trans hw').head_eq
    · exact hd m hm
  · exact ha x y hp.sound

end ExplainableCrypto.Helios.Symbolic
