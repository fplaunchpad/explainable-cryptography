import ExplainableCrypto.Helios.Symbolic.ExpandedProofTransport

namespace ExplainableCrypto.Helios.Symbolic

/-- Renaming variable handles preserves exact syntax size for every recipe. -/
theorem Term.nodeCount_subst_var {V W : Type} (r : Term V) (f : V → W) :
    (r.subst (fun v => .var (f v))).nodeCount=r.nodeCount := by
  induction r <;> simp_all only [Term.subst,Term.nodeCount]

namespace Historical.General
variable {n : Nat}

/-- All public comparisons between retained old recipes reuse the complete
initial-frame static equivalence theorem in either assignment orientation. -/
theorem expanded_old_equality_swap (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r s : Recipe 3)
    (hr : r.Public ns.restricted) (hs : s.Public ns.restricted) :
    EqE ((expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (expandedOld i))))
      ((expandedFrame ns swap left right rs).eval (s.subst (fun i => .var (expandedOld i)))) ↔
    EqE ((expandedFrame ns swap' left right rs).eval (r.subst (fun i => .var (expandedOld i))))
      ((expandedFrame ns swap' left right rs).eval (s.subst (fun i => .var (expandedOld i)))) := by
  simp only [expanded_old_recipe_value]
  cases swap <;> cases swap'
  · exact Iff.rfl
  · exact initial_frame_staticEq ns hf left right r s hr hs
  · exact (initial_frame_staticEq ns hf left right r s hr hs).symm
  · exact Iff.rfl

/-- If all source-minimum competitors of an old recipe still use old recipes,
its actual expanded minimum is shared by B7. No minimum-size transfer between
frame presentations is assumed. -/
theorem expanded_old_shared_of_minimum_origins (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r : Recipe 3) (hr : r.Public ns.restricted)
    (horigin : ∀ m, MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value m →
      EqE ((expandedFrame ns swap left right rs).eval m)
        ((expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (expandedOld i)))) →
      ∃ old : Recipe 3, old.Public ns.restricted ∧ m=old.subst (fun i => .var (expandedOld i))) :
    Frame.SharedMinimum (expandedFrame ns swap left right rs) (expandedFrame ns swap' left right rs)
      (r.subst (fun i => .var (expandedOld i))) := by
  have hp := Term.Public.subst r (fun i => Term.var (expandedOld (n := n) i)) hr (fun _ => trivial)
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hp
  obtain ⟨old,hpold,rfl⟩ := horigin m hm he.symm
  exact ⟨_,hm,he,(expanded_old_equality_swap ns hf swap swap' left right rs r old hr hpold).mp he⟩

end Historical.General
end ExplainableCrypto.Helios.Symbolic
