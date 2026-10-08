import ExplainableCrypto.Helios.Symbolic.SourceBackwardVisibleRealization

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {restricted : Finset Nat} {handles : Nat}

/-- An actual input preserves the entire canonical realization class when
its canonical visible successor is deterministic for the full evaluated recipe.
All old environment values remain constrained modulo E. -/
theorem FreeStep.input_sameRealizations_target {a b : Extended (Fin handles)}
    {c : Nat} {r : Recipe handles} (h : FreeStep a (.input c r) b)
    (φ : Frame restricted handles) (p q : Agent Empty)
    (ha : a.SameRealizations (frameProcess φ p))
    (hd : ∀ s, Agent.Visible p (.input c (φ.eval r)) s → Agent.EvalEq s q) :
    b.SameRealizations (frameProcess φ q) := by
  intro env t
  rw [frameProcess_realizes_iff]
  constructor
  · intro hb
    obtain ⟨u,s,hu,hs,he⟩ := h.realizes_backward env hb
    obtain ⟨hv,hp⟩ := (frameProcess_realizes_iff φ p env u).mp ((ha env u).mp hu)
    obtain ⟨v,hv',hj⟩ := hp.symm.input_transport hs (r.subst_congr env φ.value hv)
    exact ⟨hv,(hd v hv').symm.trans (hj.symm.trans he)⟩
  · rintro ⟨hv,ht⟩
    have hp : a.Realizes env p := (ha env p).mpr
      ((frameProcess_realizes_iff φ p env p).mpr ⟨hv,.refl _⟩)
    obtain ⟨s,hs,hb⟩ := h.input_realizes env hp
    obtain ⟨v,hv',he⟩ := (Agent.EvalEq.refl p).input_transport hs (r.subst_congr env φ.value hv)
    exact hb.congr (he.trans ((hd v hv').trans ht))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
