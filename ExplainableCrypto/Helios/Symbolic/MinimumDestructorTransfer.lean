import ExplainableCrypto.Helios.Symbolic.MinimumValueShapes

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A source minimum argument with no pair E-value cannot acquire one after the
swap. This concerns actual full-E values, not raw syntactic matching. -/
theorem minimum_no_pair_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value a)
    (hn : ∀ x y, ¬ EqE ((frame ns false left right).eval a) (.binary .pair x y))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) a.nodeCount) :
    ∀ x y, ¬ EqE ((frame ns true left right).eval a) (.binary .pair x y) := by
  intro x y he
  obtain ⟨u, v, huv⟩ := (minimum_value_shape_reflection ns left right a hm hobs).1 ⟨x, y, he⟩
  exact hn u v huv

/-- The complete syntactic minimum-decryption branch. Destination failure is
derived for all argument classes before comparing both ordered components. -/
theorem minimum_decryption_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a b c d : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .dec a b))
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .dec c d))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      ((Term.binary .dec a b).nodeCount + (Term.binary .dec c d).nodeCount)) :
    EqE ((frame ns false left right).eval (.binary .dec a b)) ((frame ns false left right).eval (.binary .dec c d)) ↔
      EqE ((frame ns true left right).eval (.binary .dec a b)) ((frame ns true left right).eval (.binary .dec c d)) := by
  have hnr := minimum_decryption_no_match ns false left right ns.restricted a b hr
  have hns := minimum_decryption_no_match ns false left right ns.restricted c d hs
  have hnr' := minimum_decryption_failure_swap ns left right a b hr
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  have hns' := minimum_decryption_failure_swap ns left right c d hs
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  have ha := hobs a c hr.isPublic.1 hs.isPublic.1 (by simp only [Term.nodeCount]; omega)
  have hb := hobs b d hr.isPublic.2 hs.isPublic.2 (by simp only [Term.nodeCount]; omega)
  exact (EqE.decryption_iff_of_no_match _ _ _ _ hnr hns).trans
    ((and_congr ha hb).trans (EqE.decryption_iff_of_no_match _ _ _ _ hnr' hns').symm)

/-- The stuck-decryption-valued branch derives raw origins from source values.
Target components may reduce; destination shapes and minimum size are absent
from the premises. -/
theorem minimum_stuck_decryption_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {a b c d : Ground} (hnr : ∀ m, ¬ DecryptionMatch a b m) (hns : ∀ m, ¬ DecryptionMatch c d m)
    (her : EqE ((frame ns false left right).eval r) (.binary .dec a b))
    (hes : EqE ((frame ns false left right).eval s) (.binary .dec c d))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨u, v, rfl, _⟩ := minimum_stuck_decryption_form ns false left right ns.restricted r hr hnr her
  obtain ⟨w, x, rfl, _⟩ := minimum_stuck_decryption_form ns false left right ns.restricted s hs hns hes
  exact minimum_decryption_equality_swap ns left right u v w x hr hs hobs

/-- The complete stuck-projection-valued branch retains both selectors and
argument values. Smaller shape reflection derives destination no-pair facts. -/
theorem minimum_stuck_projection_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    (f g : Unary) (hf : f = .fst ∨ f = .snd) (hg : g = .fst ∨ g = .snd)
    {a b : Ground} (ha : ∀ x y, ¬ EqE a (.binary .pair x y))
    (hb : ∀ x y, ¬ EqE b (.binary .pair x y))
    (her : EqE ((frame ns false left right).eval r) (.unary f a))
    (hes : EqE ((frame ns false left right).eval s) (.unary g b))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨u, rfl, hu⟩ := minimum_stuck_projection_form ns false left right ns.restricted r hr f hf ha her
  obtain ⟨v, rfl, hv⟩ := minimum_stuck_projection_form ns false left right ns.restricted s hs g hg hb hes
  have hu' := minimum_no_pair_swap ns left right u (hr.subterm (.unary f .hole)) hu
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  have hv' := minimum_no_pair_swap ns left right v (hs.subterm (.unary g .hole)) hv
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  have hab := hobs u v hr.isPublic hs.isPublic (by simp only [Term.nodeCount]; omega)
  exact (EqE.projection_iff_of_no_pair f g hf hg _ _ hu hv).trans
    ((and_congr Iff.rfl hab).trans (EqE.projection_iff_of_no_pair f g hf hg _ _ hu' hv').symm)

end ExplainableCrypto.Helios.Symbolic.Historical.General
