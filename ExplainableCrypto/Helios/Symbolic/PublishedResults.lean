import ExplainableCrypto.Helios.Symbolic.FrameExtension

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem tallyRecipe_public (rs : List (Recipe 3)) (j : Fin (n+1)) (restricted : Finset Nat)
    (hp : ∀ r ∈ rs, r.Public restricted) : (tallyRecipe rs j).Public restricted := by
  have fold (xs : List (Recipe 3)) (acc : Recipe 3) (ha : acc.Public restricted)
      (hx : ∀ r ∈ xs, r.Public restricted) :
      (xs.foldl (fun acc r => .binary .mul acc (r.project j.val)) acc).Public restricted := by
    induction xs generalizing acc with
    | nil => exact ha
    | cons r xs ih => exact ih _ ⟨ha,(hx r (by simp)).project _⟩ (fun s hs => hx s (by simp [hs]))
  exact fold rs _ ⟨(show (Term.var (1 : Fin 3)).Public restricted from trivial).project _,
    (show (Term.var (2 : Fin 3)).Public restricted from trivial).project _⟩ hp

theorem resultRecipe_public (rs : List (Recipe 3)) (restricted : Finset Nat)
    (hp : ∀ r ∈ rs, r.Public restricted) : (resultRecipe (n := n) rs).Public restricted := by
  apply candidateTuple_public
  intro j
  exact ⟨(show (Term.var (3 : Fin 4)).Public restricted from trivial).project _,
    Recipe.lift_public _ (tallyRecipe_public rs j restricted hp)⟩

theorem partialFrame_old (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (i : Fin 3) :
    (partialFrame ns swap left right rs).value i.castSucc = (frame ns swap left right).value i :=
  Frame.extend_old _ _ i

theorem finalFrame_old (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (rs : List (Recipe 3)) (i : Fin 3) :
    (finalFrame ns swap left right rs).value i.castSucc.castSucc = (frame ns swap left right).value i := by
  rw [finalFrame,Frame.extend_old,partialFrame_old]

theorem partialFrame_partial_project (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1)) :
    EqE ((partialFrame ns swap left right rs).eval ((Term.var 3).project j.val))
      (tallyPartial ns swap left right rs j) := by
  rw [Frame.eval,Term.subst_project]
  change EqE ((candidateTuple (tallyPartial ns swap left right rs)).project j.val) _
  exact candidateTuple_project _ j

theorem finalFrame_partial_project (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1)) :
    EqE ((finalFrame ns swap left right rs).eval ((Term.var 3).project j.val))
      (tallyPartial ns swap left right rs j) := by
  rw [Frame.eval,Term.subst_project]
  change EqE ((candidateTuple (tallyPartial ns swap left right rs)).project j.val) _
  exact candidateTuple_project _ j

theorem finalFrame_result_project (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1)) :
    EqE ((finalFrame ns swap left right rs).eval ((Term.var 4).project j.val))
      (tallyResult ns swap left right rs j) := by
  rw [Frame.eval,Term.subst_project]
  change EqE ((candidateTuple (tallyResult ns swap left right rs)).project j.val) _
  exact candidateTuple_project _ j

/-- Every result is already computable from the partial tuple and public
aggregate recipes. This identity requires no acceptance or equal-tally premise. -/
theorem resultRecipe_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) :
    EqE ((partialFrame ns swap left right rs).eval (resultRecipe (n := n) rs))
      (candidateTuple (tallyResult ns swap left right rs)) := by
  change EqE ((candidateTuple (fun j : Fin (n+1) => Term.binary .dec
    ((Term.var 3).project j.val) (tallyRecipe rs j).lift)).subst (partialFrame ns swap left right rs).value) _
  rw [candidateTuple_subst]
  apply EqE.candidateTuple
  intro j
  have hl : (partialFrame ns swap left right rs).eval (tallyRecipe rs j).lift =
      tallyCiphertext ns swap left right rs j := Frame.eval_extend_lift _ _ _
  change EqE (.binary .dec ((partialFrame ns swap left right rs).eval ((Term.var 3).project j.val))
    ((partialFrame ns swap left right rs).eval (tallyRecipe rs j).lift)) _
  rw [hl]
  exact .binary .dec (partialFrame_partial_project ns swap left right rs j) (.refl _)

/-- Exact reduction of final-frame equivalence to the partial-publication
frame. Neither side of this iff is asserted without proving its obligation. -/
theorem final_frame_staticEq_iff_partial (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) :
    Frame.StaticEq (finalFrame ns false left right rs) (finalFrame ns true left right rs) ↔
    Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs) :=
  Frame.StaticEq.extend_public_iff _ _ _ _ (resultRecipe (n := n) rs)
    (resultRecipe_public rs ns.restricted hp)
    (resultRecipe_value ns false left right rs) (resultRecipe_value ns true left right rs)

/-- Partial-frame equivalence retains all initial observations, but the
already-proved initial equivalence alone does not establish its converse. -/
theorem initial_staticEq_of_partial (ns : Names n)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (h : Frame.StaticEq (partialFrame ns false left right rs) (partialFrame ns true left right rs)) :
    Frame.StaticEq (frame ns false left right) (frame ns true left right) := h.of_extend

/-- Trustee partials cannot be reconstructed publicly in the initial frame.
Minimum partial-key origins would expose a public recipe for the restricted
secret. Publication therefore requires its own equivalence argument. -/
theorem initial_secret_partial_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (binding : Ground)
    (r : Recipe 3) (hr : r.Public ns.restricted) :
    ¬ EqE ((frame ns swap left right).eval r) (.binary .partialDecrypt (.name ns.secretKey) binding) := by
  intro he
  obtain ⟨m,hm,hmin⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) r hr
  have hp := hmin.symm.trans he
  obtain ⟨a,b,rfl⟩ := minimum_partial_decryption_form ns swap left right ns.restricted m hm hp
  exact frame_secret_key_not_deducible ns swap left right a hm.isPublic.1
    ((EqE.partialDecrypt_iff _ _ _ _).mp hp).1

/-- Accepted sequences give the same numeric observation at each actual final
result slot. This does not assert equality of all final-frame observations. -/
theorem final_result_numeric (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (j : Fin (n+1)) :
    ∃ k, k ≤ rs.length+2 ∧ ∀ swap : Bool,
      EqE ((finalFrame ns swap left right rs).eval ((Term.var 4).project j.val)) (addNumeral k) := by
  obtain ⟨k,hk,he⟩ := accepted_sequence_tally_numeric ns hf left right rs hp ha j
  exact ⟨k,hk,fun swap => (finalFrame_result_project ns swap left right rs j).trans (he swap)⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
