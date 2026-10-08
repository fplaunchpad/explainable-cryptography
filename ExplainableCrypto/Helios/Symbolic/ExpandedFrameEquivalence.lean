import ExplainableCrypto.Helios.Symbolic.ExpandedPublishedFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem expanded_frame_old (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (i : Fin 3) :
    (expandedFrame ns swap left right rs).value (expandedOld i) = (frame ns swap left right).value i := by
  simp [expandedFrame,expandedOld]

theorem expanded_frame_partial (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (j : Fin (n+1)) :
    (expandedFrame ns swap left right rs).value (expandedPartial j) = tallyPartial ns swap left right rs j := by
  simp [expandedFrame,expandedPartial]

theorem expanded_frame_result (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (j : Fin (n+1)) :
    (expandedFrame ns swap left right rs).value (expandedResult j) = tallyResult ns swap left right rs j := by
  simp only [expandedFrame,expandedResult,Fin.addCases_right]

theorem expandedRecipes_public (restricted : Finset Nat) (i : Fin (ExpandedHandles n)) :
    (expandedRecipes i).Public restricted := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp [expandedRecipes,Term.Public]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simpa only [expandedRecipes,Fin.addCases_right,Fin.addCases_left] using
        (show (Term.var 3 : Recipe 5).Public restricted from trivial).project j.val
    · simpa only [expandedRecipes,Fin.addCases_right] using
        (show (Term.var 4 : Recipe 5).Public restricted from trivial).project j.val

theorem tupleRecipes_public (restricted : Finset Nat) (i : Fin 5) :
    (tupleRecipes (n := n) i).Public restricted := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simpa only [tupleRecipes,Fin.lastCases_last] using
      candidateTuple_public (fun j : Fin (n+1) => (Term.var (expandedResult j))) (fun _ => trivial)
  · refine Fin.lastCases ?_ (fun j => ?_) k
    · simpa only [tupleRecipes,Fin.lastCases_castSucc,Fin.lastCases_last] using
        candidateTuple_public (fun j : Fin (n+1) => (Term.var (expandedPartial j))) (fun _ => trivial)
    · simp [tupleRecipes,Term.Public]

/-- Every individual observation is a public projection of the actual final
frame. No acceptance, freshness or submission-publicness premise is needed. -/
theorem expandedRecipes_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin (ExpandedHandles n)) :
    EqE ((finalFrame ns swap left right rs).eval (expandedRecipes i))
      ((expandedFrame ns swap left right rs).value i) := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [expandedRecipes,Fin.addCases_left,Frame.eval,Term.subst,finalFrame_old,
      expandedFrame,Fin.addCases_left]
    exact .refl _
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simpa only [expandedRecipes,expandedFrame,Fin.addCases_right,Fin.addCases_left] using
        finalFrame_partial_project ns swap left right rs j
    · simpa only [expandedRecipes,expandedFrame,Fin.addCases_right] using
        finalFrame_result_project ns swap left right rs j

/-- Public tuple reconstruction uses every candidate in the original order. -/
theorem tupleRecipes_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 5) :
    EqE ((expandedFrame ns swap left right rs).eval (tupleRecipes i))
      ((finalFrame ns swap left right rs).value i) := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · change EqE ((candidateTuple (fun j : Fin (n+1) => Term.var (expandedResult j))).subst
      (expandedFrame ns swap left right rs).value) (candidateTuple (tallyResult ns swap left right rs))
    rw [candidateTuple_subst]
    apply EqE.candidateTuple
    intro j
    simp only [Term.subst,expanded_frame_result]
    exact .refl _
  · refine Fin.lastCases ?_ (fun j => ?_) k
    · change EqE ((candidateTuple (fun j : Fin (n+1) => Term.var (expandedPartial j))).subst
        (expandedFrame ns swap left right rs).value) (candidateTuple (tallyPartial ns swap left right rs))
      rw [candidateTuple_subst]
      apply EqE.candidateTuple
      intro j
      simp only [Term.subst,expanded_frame_partial]
      exact .refl _
    · simp only [tupleRecipes,Fin.lastCases_castSucc,Frame.eval,Term.subst,expanded_frame_old,finalFrame_old]
      exact .refl _

/-- This is an exact change of public presentation, not a proof of either
swapped-frame equivalence. Both directions retain all observations. -/
theorem expanded_frame_staticEq_iff_final (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) ↔
    Frame.StaticEq (finalFrame ns false left right rs) (finalFrame ns true left right rs) := by
  constructor
  · intro h
    exact (Frame.staticEq_of_pointwise (tupleRecipes_value ns false left right rs)).symm.trans
      ((h.derive tupleRecipes (tupleRecipes_public ns.restricted)).trans
        (Frame.staticEq_of_pointwise (tupleRecipes_value ns true left right rs)))
  · intro h
    exact (Frame.staticEq_of_pointwise (expandedRecipes_value ns false left right rs)).symm.trans
      ((h.derive expandedRecipes (expandedRecipes_public ns.restricted)).trans
        (Frame.staticEq_of_pointwise (expandedRecipes_value ns true left right rs)))

theorem expanded_frame_staticEq_iff_partial (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) :
    Frame.StaticEq (expandedFrame ns false left right rs) (expandedFrame ns true left right rs) ↔
    Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs) :=
  (expanded_frame_staticEq_iff_final ns left right rs).trans (final_frame_staticEq_iff_partial ns left right rs hp)

/-- Name protection follows by public projection from the existing final-frame
invariant. This avoids assuming an invariant for a newly defined frame. -/
theorem expanded_frame_opaque_protected (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) : (expandedFrame ns swap left right rs).OpaqueProtected := by
  intro i
  exact ((final_frame_opaque_protected ns swap left right rs hp).eval (expandedRecipes i)
    (expandedRecipes_public ns.restricted i)).of_eq (expandedRecipes_value ns swap left right rs i)

/-- Arbitrary initial recipes retain their exact values under the old-handle
embedding. No claim about preserving their minimum syntax size is made. -/
theorem expanded_old_recipe_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (r : Recipe 3) :
    (expandedFrame ns swap left right rs).eval (r.subst (fun i => .var (expandedOld i))) =
      (frame ns swap left right).eval r := by
  simp only [Frame.eval,Term.subst_subst,Term.subst,expanded_frame_old]

end ExplainableCrypto.Helios.Symbolic.Historical.General
