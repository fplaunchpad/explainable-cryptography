import ExplainableCrypto.Helios.Symbolic.MixedFusion

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

theorem OuterFusion.of_base {a b u v : Term V} (h : OuterFusion a b)
    (hu : BaseEq u a) (hv : BaseEq b v) : OuterFusion u v := by
  unfold OuterFusion at *
  simpa only [hu.mul_factors, ← hv.mul_factors] using h

theorem FactorStep.of_base {a b u v : Term V} (h : FactorStep a b)
    (hu : BaseEq u a) (hv : BaseEq b v) : FactorStep u v := by
  obtain ⟨x, y, rest, hx, hxy, ha, hb⟩ := h
  exact ⟨x, y, rest, hx, hxy, hu.mul_factors.trans ha, hv.mul_factors.symm.trans hb⟩

theorem OuterFusion.mul_right {a b : Term V} (h : OuterFusion a b) (t : Term V) :
    OuterFusion (.binary .mul a t) (.binary .mul b t) := by
  obtain ⟨inputs, output, rest, hr, ha, hb⟩ := h
  exact ⟨inputs, output, rest + t.mulFactors, hr,
    by simp only [Term.mulFactors, ha, Multiset.add_assoc],
    by simp only [Term.mulFactors, hb, Multiset.add_assoc]⟩

theorem FactorStep.mul_right {a b : Term V} (h : FactorStep a b) (t : Term V) :
    FactorStep (.binary .mul a t) (.binary .mul b t) := by
  obtain ⟨x, y, rest, hx, hxy, ha, hb⟩ := h
  exact ⟨x, y, rest + t.mulFactors, hx, hxy,
    by simp only [Term.mulFactors, ha, Multiset.add_assoc],
    by simp only [Term.mulFactors, hb, Multiset.add_assoc]⟩

theorem OuterFusion.mul_left {a b : Term V} (h : OuterFusion a b) (t : Term V) :
    OuterFusion (.binary .mul t a) (.binary .mul t b) :=
  (h.mul_right t).of_base (.equation (.comm .mul trivial _ _))
    (.equation (.comm .mul trivial _ _))

theorem FactorStep.mul_left {a b : Term V} (h : FactorStep a b) (t : Term V) :
    FactorStep (.binary .mul t a) (.binary .mul t b) :=
  (h.mul_right t).of_base (.equation (.comm .mul trivial _ _))
    (.equation (.comm .mul trivial _ _))

theorem FactorStep.of_singleton {a b : Term V} (h : RewriteStep a b)
    (ha : a.mulFactors = {a.baseClass}) : FactorStep a b :=
  ⟨a, b, 0, ha, ⟨a, b, .refl _, h, .refl _⟩, by simpa using ha, by simp⟩

/-- All contexts are covered: an outer multiplication extends the remainder;
any other enclosing constructor makes the whole context a single factor. -/
theorem RewriteStep.factor_cases {a b : Term V} (h : RewriteStep a b) :
    OuterFusion a b ∨ FactorStep a b := by
  obtain ⟨c, l, r, hr, rfl, rfl⟩ := h
  induction c with
  | hole =>
    cases hr with
    | homomorphic k r s m n =>
      exact Or.inl (OuterFusion.of_factors _ _ k r s m n 0
        (by simp [Context.fill, Term.mulFactors, ciphertextPairFactors])
        (by simp [Context.fill, Term.mulFactors]))
    | _ => exact Or.inr (FactorStep.of_singleton ⟨.hole, _, _, by constructor, rfl, rfl⟩ rfl)
  | binaryLeft f c t ih =>
    cases f with
    | mul => exact ih.elim (fun h => Or.inl (h.mul_right t)) (fun h => Or.inr (h.mul_right t))
    | _ => exact Or.inr (FactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl)
  | binaryRight f t c ih =>
    cases f with
    | mul => exact ih.elim (fun h => Or.inl (h.mul_left t)) (fun h => Or.inr (h.mul_left t))
    | _ => exact Or.inr (FactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl)
  | _ => exact Or.inr (FactorStep.of_singleton ⟨_, l, r, hr, rfl, rfl⟩ rfl)

/-- E0 changes in either endpoint preserve the exhaustive step classification. -/
theorem ModuloStep.factor_cases {a b : Term V} (h : ModuloStep a b) :
    OuterFusion a b ∨ FactorStep a b := by
  obtain ⟨x, y, hx, hxy, hy⟩ := h
  exact hxy.factor_cases.elim (fun h => Or.inl (h.of_base hx hy))
    (fun h => Or.inr (h.of_base hx hy))

/-- Any peak with at least one outer fusion is now covered, including arbitrary
contexts and E0 representatives on the other step. -/
theorem outer_fusion_modulo_peak_joined {a b c : Term V}
    (hf : OuterFusion a b) (hc : ModuloStep a c) : JoinModulo b c := by
  rcases hc.factor_cases with hc | hc
  · exact (outer_fusion_peak_joined hf hc).2.2
  · exact (fusion_factor_peak_joined hf hc).2.2

end ExplainableCrypto.Helios.Symbolic
