import ExplainableCrypto.Helios.Symbolic.ExpandedValueOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem voter_not_pk (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2)
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain (expandedOld i.succ) r) (key : Ground) :
    ¬ EqE ((expandedFrame ns swap left right rs).eval r) (.unary .pk key) := by
  have hv : EqE ((expandedFrame ns swap left right rs).value (expandedOld i.succ))
      (Term.tuple (ballotFields ns i (choice swap left right i).value)) := by
    rw [expanded_frame_old,frame_voter_handle]
    exact .refl _
  exact hc.not_pk_of_tuple _ hv (ballot_fields_not_pair ns i _) (ballot_fields_not_pk ns i _) key

private theorem numeral_not_pair (number : Nat) (x y : Ground) :
    ¬ EqE (addNumeral number) (.binary .pair x y) := by
  intro he
  have hh := (addNumeral_irreducible number).pair_head_of_eq he
  cases number <;> cases hh

private theorem numeral_not_pk (number : Nat) (key : Ground) :
    ¬ EqE (addNumeral number) (.unary .pk key) := by
  intro he
  obtain ⟨_,hshape,_⟩ := he.symm.pk_irreducible_shape (addNumeral_irreducible number)
  cases number <;> cases hshape

private theorem partial_not_pair (key binding x y : Ground) :
    ¬ EqE (.binary .partialDecrypt key binding) (.binary .pair x y) := by
  intro he
  have hf := ((EqE.passive_binary_iff .partialDecrypt .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp he).1
  cases hf

/-- Among all expanded-frame selector chains, only the retained election-key
handle has a pk value. Opaque partials and numeric results add no key selector. -/
theorem expanded_projection_pk_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain v r) {key : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.unary .pk key)) :
    r = .var (expandedOld 0) := by
  have handle {v : Fin (ExpandedHandles n)} {r : Recipe (ExpandedHandles n)}
      (hc : ProjectionChain v r)
      (hp : ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).value v) (.binary .pair x y))
      (he : EqE ((expandedFrame ns swap left right rs).eval r) (.unary .pk key)) : r = .var v := by
    cases hc with
    | handle => rfl
    | step f hf hc =>
      obtain ⟨x,y,hpair,_⟩ := he.projection_pk_inversion hf
      exact False.elim (hc.not_pair_of_handle hp x y hpair.sound)
  revert hc he
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro hc he
    fin_cases old
    · exact handle hc (fun x y h => pk_not_eqE_pair _ x y
        (by simpa [expandedFrame,expandedOld,frame,publicKey] using h)) he
    · exact False.elim (voter_not_pk ns swap left right rs 0 hc key he)
    · exact False.elim (voter_not_pk ns swap left right rs 1 hc key he)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro hc he
      have hr := handle hc (fun x y h => partial_not_pair _ _ x y
        (by simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left,tallyPartial] using h)) he
      subst r
      exact False.elim (pk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) key _ _
        (by simpa only [Frame.eval,Term.subst,expandedFrame,Fin.addCases_right,Fin.addCases_left,tallyPartial] using he.symm))
    · intro hc he
      obtain ⟨number,hnum⟩ := hn j
      have hr := handle hc (fun x y h => numeral_not_pair number x y
        (hnum.symm.trans (by simpa only [expandedFrame,Fin.addCases_right] using h))) he
      subst r
      exact False.elim (numeral_not_pk number key (hnum.symm.trans
        (by simpa only [Frame.eval,Term.subst,expandedFrame,Fin.addCases_right] using he)))

/-- The two minimum key forms in the expanded proof presentation. -/
def ExpandedPublicKeyRecipeForm (r : Recipe (ExpandedHandles n)) : Prop :=
  r = .var (expandedOld 0) ∨ ∃ a, r = .unary .pk a

theorem expanded_minimum_public_key_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r) {key : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.unary .pk key)) : ExpandedPublicKeyRecipeForm r :=
  (expandedFrame ns swap left right rs).minimum_public_key_form_of_origins restricted (expandedOld 0)
    (fun r hm _ _ he => expanded_minimum_pair_origin ns swap left right rs hn restricted r hm he)
    (fun a b hm out => expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm out)
    (fun v _ hc _ he => expanded_projection_pk_origin ns swap left right rs hn v hc he) r hm he

/-- Actual accepted elections discharge every expanded-frame origin premise. -/
theorem accepted_expanded_minimum_public_key_form (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) (swap : Bool)
    (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r) {key : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.unary .pk key)) : ExpandedPublicKeyRecipeForm r :=
  expanded_minimum_public_key_form ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted r hm he

end ExplainableCrypto.Helios.Symbolic.Historical.General
