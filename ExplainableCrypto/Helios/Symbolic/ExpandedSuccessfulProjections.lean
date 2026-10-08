import ExplainableCrypto.Helios.Symbolic.ExpandedPairTransport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

def ExpandedHonestProjectionForm (f : Unary) (a : Recipe (ExpandedHandles n)) : Prop :=
  ∃ i : Fin 2, ∃ k, k < fieldCount n ∧ a = (Term.var (expandedOld i.succ)).drop k ∧
    (f = .fst ∨ f = .snd ∧ k+1 < fieldCount n)

/-- A successful minimum projection selects old honest data. An empty-tail
result has a smaller literal bottom recipe and is excluded from this form. -/
theorem expanded_minimum_successful_projection_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat) (f : Unary)
    (hf : f = .fst ∨ f = .snd) (a : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value (.unary f a))
    {x y : Ground} (hp : EqE ((expandedFrame ns swap left right rs).eval a) (.binary .pair x y)) :
    ExpandedHonestProjectionForm f a := by
  have harg := expanded_minimum_pair_origin ns swap left right rs hn restricted a (hm.subterm (.unary f .hole)) hp
  obtain ⟨v,hc⟩ := hm.projection_chain_of_pair_origin hf harg
  cases hc with
  | step _ _ hc =>
    obtain ⟨i,k,hk,rfl⟩ := expanded_projection_pair_origin ns swap left right rs hn v hc hp
    refine ⟨i,k,hk,rfl,?_⟩
    rcases hf with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl,?_⟩
      by_contra hlast
      have ht := expanded_ballot_tail_value ns swap left right rs i (k+1) (by omega)
      have hempty : (ballotFields ns i (choice swap left right i).value).drop (k+1) = [] :=
        List.drop_eq_nil_of_le (by rw [ballot_fields_length]; omega)
      have hout : EqE ((expandedFrame ns swap left right rs).eval (.unary .snd ((Term.var (expandedOld i.succ)).drop k)))
          (.const .bottom) := by
        simpa only [Term.drop_succ_outer,hempty,Term.tuple] using ht
      exact hm.no_smaller (s := .const .bottom) trivial hout
        (by have := ((Term.var (expandedOld (n := n) i.succ) : Recipe (ExpandedHandles n)).drop k).nodeCount_pos
            simp only [Term.nodeCount]; omega)

theorem ExpandedHonestProjectionForm.argument_pair_path {f : Unary} {a : Recipe (ExpandedHandles n)}
    (h : ExpandedHonestProjectionForm f a) (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) :
    ∃ x y, ReducesModulo ((expandedFrame ns swap left right rs).eval a) (.binary .pair x y) := by
  obtain ⟨i,k,hk,rfl,_⟩ := h
  obtain ⟨x,y,he⟩ := expanded_ballot_tail_pair_value ns swap left right rs i k hk
  exact he.reaches_pair

/-- Data classification reuses the original honest projection theorem through
retained handle values. It excludes successful outputs in new value classes. -/
theorem ExpandedHonestProjectionForm.data_value {f : Unary} {a : Recipe (ExpandedHandles n)}
    (h : ExpandedHonestProjectionForm f a) (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) :
    (∃ x y, EqE ((expandedFrame ns swap left right rs).eval (.unary f a)) (.binary .pair x y)) ∨
    (∃ k r m, EqE ((expandedFrame ns swap left right rs).eval (.unary f a)) (.ternary .penc k r m)) ∨
    (∃ k r m c, EqE ((expandedFrame ns swap left right rs).eval (.unary f a)) (.spk k r m c)) := by
  obtain ⟨i,k,hk,rfl,hf⟩ := h
  have hold : HonestProjectionForm n f ((Term.var i.succ).drop k) := ⟨i,k,hk,rfl,hf⟩
  simpa only [Frame.eval,Term.subst,Term.subst_drop,expanded_frame_old] using hold.data_value ns swap left right

end ExplainableCrypto.Helios.Symbolic.Historical.General
