import ExplainableCrypto.Helios.Symbolic.AtomicObservationOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A minimum initial-frame recipe for a ground atom is literal syntax, so its
value is exactly that atom in any other frame with the same recipe type. This
does not assert transport of arbitrary nonminimum evaluations. -/
theorem minimum_atomic_eval_any_frame (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r)
    (t : Ground) (ht : t.nodeCount = 1)
    (he : EqE ((frame ns swap left right).eval r) t) (ψ : Frame restricted 3) : ψ.eval r = t := by
  rcases ground_atom_cases ht with ⟨name, rfl⟩ | ⟨c, rfl⟩
  · rw [minimum_name_form ns swap left right restricted r hm name he]
    rfl
  · rw [minimum_constant_form ns swap left right restricted r hm c he]
    rfl

/-- Minimum atomic observations compare the literal atom values, including all
name/name, name/constant and constant/constant cases. -/
theorem minimum_atomic_equality_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r s : Recipe 3)
    (hr : MinimalRecipe restricted (frame ns swap left right).value r)
    (hs : MinimalRecipe restricted (frame ns swap left right).value s)
    (a b : Ground) (ha : a.nodeCount = 1) (hb : b.nodeCount = 1)
    (her : EqE ((frame ns swap left right).eval r) a)
    (hes : EqE ((frame ns swap left right).eval s) b) (ψ : Frame restricted 3) :
    EqE (ψ.eval r) (ψ.eval s) ↔ a = b := by
  rw [minimum_atomic_eval_any_frame ns swap left right restricted r hr a ha her ψ,
    minimum_atomic_eval_any_frame ns swap left right restricted s hs b hb hes ψ]
  exact EqE.ground_atoms_iff a b ha hb

/-- The atomic minimum-recipe branch needs no smaller-observation or freshness
premise: both recipes are forced to be literal public atoms. -/
theorem minimum_atomic_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    (a b : Ground) (ha : a.nodeCount = 1) (hb : b.nodeCount = 1)
    (her : EqE ((frame ns false left right).eval r) a)
    (hes : EqE ((frame ns false left right).eval s) b) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) :=
  (minimum_atomic_equality_iff ns false left right ns.restricted r s hr hs a b ha hb her hes _).trans
    (minimum_atomic_equality_iff ns false left right ns.restricted r s hr hs a b ha hb her hes _).symm

end ExplainableCrypto.Helios.Symbolic.Historical.General
