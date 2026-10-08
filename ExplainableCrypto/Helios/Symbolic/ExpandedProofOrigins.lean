import ExplainableCrypto.Helios.Symbolic.ExpandedValueOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The two honest selector forms, with the original ballot handles retained. -/
def ExpandedBorrowedProofForm (r : Recipe (ExpandedHandles n)) : Prop :=
  (∃ i : Fin 2, ∃ j : Fin (n+1), r = (Term.var (expandedOld i.succ)).project (n+1+j.val)) ∨
  (∃ i : Fin 2, r = (Term.var (expandedOld i.succ)).project (2*(n+1)))

def ExpandedProofRecipeForm (r : Recipe (ExpandedHandles n)) : Prop :=
  (∃ a b c d, r = .spk a b c d) ∨ ExpandedBorrowedProofForm r

private theorem voter_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2)
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain (expandedOld i.succ) r)
    {a b c d : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.spk a b c d)) :
    ExpandedBorrowedProofForm r := by
  have hv : EqE ((expandedFrame ns swap left right rs).value (expandedOld i.succ))
      (Term.tuple (ballotFields ns i (choice swap left right i).value)) := by
    rw [expanded_frame_old,frame_voter_handle]
    exact .refl _
  obtain ⟨idx,hi,hr,hval⟩ := hc.proof_origin _ hv (ballot_fields_not_pair ns i _) he
  rcases ballot_field_cases ns i (choice swap left right i).value idx hi with
    ⟨j,_,hfield⟩ | ⟨j,rfl,hfield⟩ | ⟨rfl,hfield⟩
  · rw [hfield] at hval
    exact False.elim (penc_not_eqE_spk _ _ _ _ _ _ _ hval)
  · exact Or.inl ⟨i,j,hr⟩
  · exact Or.inr ⟨i,hr⟩

private theorem numeral_not_pair (number : Nat) (x y : Ground) :
    ¬ EqE (addNumeral number) (.binary .pair x y) := by
  intro he
  have hh := (addNumeral_irreducible number).pair_head_of_eq he
  cases number <;> cases hh

private theorem numeral_not_spk (number : Nat) (a b c d : Ground) :
    ¬ EqE (addNumeral number) (.spk a b c d) := by
  intro he
  obtain ⟨_,_,_,_,hshape,_⟩ := he.symm.spk_irreducible_shape (addNumeral_irreducible number)
  cases number <;> cases hshape

/-- Publication adds no proof-valued selector chain. Every borrowed proof
still comes from a component or aggregate field of an original honest ballot. -/
theorem expanded_projection_proof_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain v r) {a b c d : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.spk a b c d)) :
    ExpandedBorrowedProofForm r := by
  have reject {v : Fin (ExpandedHandles n)} {r : Recipe (ExpandedHandles n)}
      (hc : ProjectionChain v r)
      (hp : ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).value v) (.binary .pair x y))
      (hs : ¬ EqE ((expandedFrame ns swap left right rs).value v) (.spk a b c d))
      (he : EqE ((expandedFrame ns swap left right rs).eval r) (.spk a b c d)) : False := by
    cases hc with
    | handle => exact hs he
    | step f hf hc =>
      obtain ⟨x,y,hpair,_⟩ := he.projection_spk_inversion hf
      exact hc.not_pair_of_handle hp x y hpair.sound
  revert hc he
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro hc he
    fin_cases old
    · exact False.elim (reject hc
        (fun x y h => pk_not_eqE_pair _ x y (by simpa [expandedFrame,expandedOld,frame,publicKey] using h))
        (fun h => pk_not_eqE_spk _ a b c d (by simpa [expandedFrame,expandedOld,frame,publicKey] using h)) he)
    · exact voter_origin ns swap left right rs 0 hc he
    · exact voter_origin ns swap left right rs 1 hc he
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro hc he
      apply False.elim (reject hc ?_ ?_ he)
      · intro x y h
        have hval : EqE (tallyPartial ns swap left right rs j) (.binary .pair x y) := by
          simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left] using h
        have hf := ((EqE.passive_binary_iff .partialDecrypt .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp hval).1
        cases hf
      · intro h
        exact spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) a b c d _ _
          (by simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left,tallyPartial] using h.symm)
    · intro hc he
      obtain ⟨number,hnum⟩ := hn j
      exact False.elim (reject hc
        (fun x y h => numeral_not_pair number x y (hnum.symm.trans
          (by simpa only [expandedFrame,Fin.addCases_right] using h)))
        (fun h => numeral_not_spk number a b c d (hnum.symm.trans
          (by simpa only [expandedFrame,Fin.addCases_right] using h))) he)

theorem expanded_minimum_proof_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {a b c d : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.spk a b c d)) :
    ExpandedProofRecipeForm r := by
  rcases (expandedFrame ns swap left right rs).minimum_proof_origin_of_origins restricted
      (fun r hm _ _ he => expanded_minimum_pair_origin ns swap left right rs hn restricted r hm he)
      (fun a b hm out => expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm out)
      r hm he with h | ⟨v,hc⟩
  · exact Or.inl h
  · exact Or.inr (expanded_projection_proof_origin ns swap left right rs hn v hc he)

theorem accepted_expanded_minimum_proof_form (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) (swap : Bool)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    {a b c d : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.spk a b c d)) :
    ExpandedProofRecipeForm r :=
  expanded_minimum_proof_form ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted r hm he

end ExplainableCrypto.Helios.Symbolic.Historical.General
