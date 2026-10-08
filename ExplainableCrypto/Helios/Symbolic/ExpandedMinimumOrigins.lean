import ExplainableCrypto.Helios.Symbolic.ExpandedFrameEquivalence

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- A minimum recipe equal to an existing public handle attains the universal
one-node lower bound. This compares recipes within the same frame. -/
theorem Frame.minimum_handle_value_size_one (φ : Frame restricted handles) (r : Recipe handles)
    (hm : MinimalRecipe restricted φ.value r) (i : Fin handles) (he : EqE (φ.eval r) (φ.value i)) :
    r.nodeCount = 1 := by
  have hle : r.nodeCount ≤ 1 := hm.least (.var i) trivial he
  have hpos := r.nodeCount_pos
  omega

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

theorem expanded_minimum_partial_size_one (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1))
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (tallyPartial ns swap left right rs j)) :
    r.nodeCount = 1 :=
  (expandedFrame ns swap left right rs).minimum_handle_value_size_one r hm (expandedPartial j)
    (by simpa only [expanded_frame_partial] using he)

theorem expanded_minimum_result_size_one (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1))
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (tallyResult ns swap left right rs j)) :
    r.nodeCount = 1 :=
  (expandedFrame ns swap left right rs).minimum_handle_value_size_one r hm (expandedResult j)
    (by simpa only [expanded_frame_result] using he)

/-- Results have public handle shortcuts, including results whose explicit
numeral syntax would be larger than the decryption recipe. -/
theorem expanded_decryption_not_minimal_of_result (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1))
    (a b : Recipe (ExpandedHandles n))
    (he : EqE ((expandedFrame ns swap left right rs).eval (.binary .dec a b)) (tallyResult ns swap left right rs j)) :
    ¬ MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b) := by
  intro hm
  have hs := expanded_minimum_result_size_one ns swap left right rs j _ hm he
  have ha := a.nodeCount_pos
  have hb := b.nodeCount_pos
  simp only [Term.nodeCount] at hs
  omega

theorem expanded_bound_tally_decryption_not_minimal (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1))
    (a b : Recipe (ExpandedHandles n))
    (ha : EqE ((expandedFrame ns swap left right rs).eval a) (tallyPartial ns swap left right rs j))
    (hb : EqE ((expandedFrame ns swap left right rs).eval b) (tallyCiphertext ns swap left right rs j)) :
    ¬ MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b) :=
  expanded_decryption_not_minimal_of_result ns swap left right rs j a b (.binary .dec ha hb)

/-- A semantic E6 binding with a borrowed trustee partial forces the complete
tally binding. Its result handle contradicts whole-recipe minimality. E5 is
not excluded by this theorem. -/
theorem expanded_minimum_decryption_no_trustee_E6 (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (j : Fin (n+1))
    (a b : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b))
    (ha : EqE ((expandedFrame ns swap left right rs).eval a) (tallyPartial ns swap left right rs j))
    (k : Ground) (he : EqE ((expandedFrame ns swap left right rs).eval a)
      (.binary .partialDecrypt k ((expandedFrame ns swap left right rs).eval b))) : False := by
  have hb := ((EqE.partialDecrypt_iff _ _ _ _).mp (ha.symm.trans he)).2.symm
  exact expanded_bound_tally_decryption_not_minimal ns swap left right rs j a b ha hb hm

private theorem numeral_not_partial (k : Nat) (a b : Ground) :
    ¬ EqE (addNumeral k) (.binary .partialDecrypt a b) := by
  cases k with
  | zero =>
    intro he
    obtain ⟨_,_,hshape,_⟩ := he.symm.passive_binary_irreducible_shape
      (Or.inr rfl) (constant_irreducible .zero)
    cases hshape
  | succ k =>
    exact arithmetic_not_eqE_passive_binary .add .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _

/-- In an accepted election, a minimum recipe for a published trustee partial
is a partial-slot handle. Initial handles, names, constants and numeric result
slots are excluded. Aliasing between partial slots remains explicit. -/
theorem expanded_minimum_trustee_partial_origin (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (swap : Bool) (j : Fin (n+1)) (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (tallyPartial ns swap left right rs j)) :
    ∃ i : Fin (n+1), r = .var (expandedPartial i) ∧
      EqE (tallyCiphertext ns swap left right rs i) (tallyCiphertext ns swap left right rs j) := by
  have hs := expanded_minimum_partial_size_one ns swap left right rs j r hm he
  rcases r.nodeCount_one_cases (by omega) with ⟨name,rfl⟩ | ⟨v,rfl⟩ | ⟨c,rfl⟩
  · obtain ⟨_,_,hshape,_⟩ := he.symm.passive_binary_irreducible_shape
      (Or.inr rfl) (name_irreducible name)
    cases hshape
  · revert he
    refine Fin.addCases (fun i => ?_) (fun k => ?_) v
    · intro he
      simp only [Frame.eval,Term.subst,expandedFrame,Fin.addCases_left] at he
      exact False.elim (initial_secret_partial_not_deducible ns swap left right _ (.var i) trivial he)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · intro he
        simp only [Frame.eval,Term.subst,expandedFrame,Fin.addCases_right,Fin.addCases_left] at he
        exact ⟨i,rfl,(tally_partial_eq_iff ns swap left right rs i j).mp he⟩
      · intro he
        simp only [Frame.eval,Term.subst,expandedFrame,Fin.addCases_right] at he
        obtain ⟨number,_,hnum⟩ := accepted_sequence_tally_numeric ns hf left right rs hp ha i
        exact False.elim (numeral_not_partial number _ _ ((hnum swap).symm.trans he))
  · obtain ⟨_,_,hshape,_⟩ := he.symm.passive_binary_irreducible_shape
      (Or.inr rfl) (constant_irreducible c)
    cases hshape

end ExplainableCrypto.Helios.Symbolic.Historical.General
