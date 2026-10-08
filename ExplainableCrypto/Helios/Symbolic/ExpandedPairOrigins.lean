import ExplainableCrypto.Helios.Symbolic.ExpandedValueOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Expanded pair values are explicit pairs or nonempty tails of old ballots. -/
def ExpandedPairObservationForm (r : Recipe (ExpandedHandles n)) : Prop :=
  (∃ a b, r = .binary .pair a b) ∨
    ∃ i : Fin 2, ∃ k, k < fieldCount n ∧ r = (Term.var (expandedOld i.succ)).drop k

private theorem voter_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2)
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain (expandedOld i.succ) r)
    {a b : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .pair a b)) :
    ∃ k, k < fieldCount n ∧ r = (Term.var (expandedOld i.succ)).drop k := by
  have hv : EqE ((expandedFrame ns swap left right rs).value (expandedOld i.succ))
      (Term.tuple (ballotFields ns i (choice swap left right i).value)) := by
    rw [expanded_frame_old,frame_voter_handle]
    exact .refl _
  obtain ⟨k,hk,hr⟩ := hc.pair_origin _ hv (ballot_fields_not_pair ns i _) he
  exact ⟨k,by simpa only [ballot_fields_length] using hk,hr⟩

private theorem numeral_not_pair (number : Nat) (a b : Ground) :
    ¬ EqE (addNumeral number) (.binary .pair a b) := by
  intro he
  have hh := (addNumeral_irreducible number).pair_head_of_eq he
  cases number <;> cases hh

theorem expanded_projection_pair_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n))
    {r : Recipe (ExpandedHandles n)} (hc : ProjectionChain v r) {a b : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .pair a b)) :
    ∃ i : Fin 2, ∃ k, k < fieldCount n ∧ r = (Term.var (expandedOld i.succ)).drop k := by
  revert hc he
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro hc he
    fin_cases old
    · exact False.elim (hc.not_pair_of_handle
        (fun x y h => pk_not_eqE_pair _ x y (by simpa [expandedFrame,expandedOld,frame,publicKey] using h)) a b he)
    · obtain ⟨k,hk,hr⟩ := voter_origin ns swap left right rs 0 hc he
      exact ⟨0,k,hk,hr⟩
    · obtain ⟨k,hk,hr⟩ := voter_origin ns swap left right rs 1 hc he
      exact ⟨1,k,hk,hr⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro hc he
      apply False.elim (hc.not_pair_of_handle ?_ a b he)
      intro x y h
      have hval : EqE (tallyPartial ns swap left right rs j) (.binary .pair x y) := by
        simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left] using h
      have hf := ((EqE.passive_binary_iff .partialDecrypt .pair (Or.inr rfl) (Or.inl rfl) _ _ _ _).mp hval).1
      cases hf
    · intro hc he
      obtain ⟨number,hnum⟩ := hn j
      exact False.elim (hc.not_pair_of_handle
        (fun x y h => numeral_not_pair number x y (hnum.symm.trans
          (by simpa only [expandedFrame,Fin.addCases_right] using h))) a b he)

theorem expanded_minimum_pair_observation_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {a b : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .pair a b)) :
    ExpandedPairObservationForm r := by
  rcases expanded_minimum_pair_origin ns swap left right rs hn restricted r hm he with h | ⟨v,hc⟩
  · exact Or.inl h
  · exact Or.inr (expanded_projection_pair_origin ns swap left right rs hn v hc he)

theorem accepted_expanded_minimum_pair_observation_form (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs) (swap : Bool)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    {a b : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .pair a b)) :
    ExpandedPairObservationForm r :=
  expanded_minimum_pair_observation_form ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted r hm he

theorem expanded_ballot_tail_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2) (k : Nat) (hk : k ≤ fieldCount n) :
    EqE ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).drop k))
      (Term.tuple ((ballotFields ns i (choice swap left right i).value).drop k)) := by
  simpa only [Frame.eval,Term.subst_drop,Term.subst,expanded_frame_old,frame_voter_handle,ballot] using
    (tuple_drop_reduces (ballotFields ns i (choice swap left right i).value) k
      (by simpa only [ballot_fields_length] using hk)).sound

theorem expanded_ballot_tail_pair_value (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i : Fin 2) (k : Nat) (hk : k < fieldCount n) :
    ∃ a b, EqE ((expandedFrame ns swap left right rs).eval ((Term.var (expandedOld i.succ)).drop k)) (.binary .pair a b) := by
  have h := ballot_tail_pair_value ns swap left right i k hk
  simpa only [Frame.eval,Term.subst_drop,Term.subst,expanded_frame_old] using h

/-- Classified pair syntax supplies pair-valuedness in either world, without
assuming destination minimality, freshness, acceptance or observations. -/
theorem ExpandedPairObservationForm.pair_value {r : Recipe (ExpandedHandles n)} (h : ExpandedPairObservationForm r)
    (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) :
    ∃ a b, EqE ((expandedFrame ns swap left right rs).eval r) (.binary .pair a b) := by
  rcases h with ⟨a,b,rfl⟩ | ⟨i,k,hk,rfl⟩
  · exact ⟨_,_,.refl _⟩
  · exact expanded_ballot_tail_pair_value ns swap left right rs i k hk

end ExplainableCrypto.Helios.Symbolic.Historical.General
