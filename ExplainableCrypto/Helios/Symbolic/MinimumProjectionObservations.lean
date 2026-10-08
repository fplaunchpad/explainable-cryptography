import ExplainableCrypto.Helios.Symbolic.ProofCheckObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A full-E pair value has an actual path to a pair, with potentially reduced
components. No literal input shape or target normality is required. -/
theorem EqE.reaches_pair {t a b : Term V} (he : EqE t (.binary .pair a b)) :
    ∃ x y, ReducesModulo t (.binary .pair x y) := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp he
  obtain ⟨x, y, hw, _⟩ := hr.passive_binary_components (Or.inl rfl)
  exact ⟨x, y, hl.trans (.base hw)⟩

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- A successful minimum projection selects an honest field or retains a
nonempty honest tail. The argument syntax and terminal bound remain explicit. -/
def HonestProjectionForm (n : Nat) (f : Unary) (a : Recipe 3) : Prop :=
  ∃ i : Fin 2, ∃ k, k < fieldCount n ∧ a = (Term.var i.succ).drop k ∧
    (f = .fst ∨ f = .snd ∧ k + 1 < fieldCount n)

theorem minimum_successful_projection_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (f : Unary)
    (hf : f = .fst ∨ f = .snd) (a : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value (.unary f a))
    {x y : Ground} (hp : EqE ((frame ns swap left right).eval a) (.binary .pair x y)) :
    HonestProjectionForm n f a := by
  have harg := minimum_pair_origin ns swap left right restricted a (hm.subterm (.unary f .hole)) hp
  obtain ⟨v, hc⟩ := hm.projection_chain_of_pair_origin hf harg
  cases hc with
  | step _ _ hc =>
    obtain ⟨i, k, hk, rfl⟩ := frame_projection_pair_origin ns swap left right v hc hp
    refine ⟨i, k, hk, rfl, ?_⟩
    rcases hf with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl, ?_⟩
      by_contra hlast
      have heq : k + 1 = fieldCount n := by omega
      have ht := ballot_tail_recipe_value ns swap left right i (k + 1) (by omega)
      have hempty : (ballotFields ns i (choice swap left right i).value).drop (k + 1) = [] :=
        List.drop_eq_nil_of_le (by rw [ballot_fields_length]; omega)
      have hout : EqE ((frame ns swap left right).eval (.unary .snd ((Term.var i.succ).drop k)))
          (.const .bottom) := by
        simpa only [Term.drop_succ_outer, hempty, Term.tuple] using ht
      have hs := minimum_constant_form ns swap left right restricted
        (.unary .snd ((Term.var i.succ).drop k)) hm .bottom hout
      cases hs

/-- Classified successful projections still reach an actual argument pair for
any other valid candidate assignment. No destination minimum premise is needed. -/
theorem HonestProjectionForm.argument_pair_path {f : Unary} {a : Recipe 3}
    (h : HonestProjectionForm n f a) (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) :
    ∃ x y, ReducesModulo ((frame ns swap left right).eval a) (.binary .pair x y) := by
  obtain ⟨i, k, hk, rfl, _⟩ := h
  obtain ⟨x, y, he⟩ := ballot_tail_pair_value ns swap left right i k hk
  exact he.reaches_pair

/-- The output is honest tuple data: a nonempty tail, ciphertext or proof.
Neither bottom nor an arbitrary constructor value is added to this class. -/
theorem HonestProjectionForm.data_value {f : Unary} {a : Recipe 3}
    (h : HonestProjectionForm n f a) (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) :
    (∃ x y, EqE ((frame ns swap left right).eval (.unary f a)) (.binary .pair x y)) ∨
    (∃ k r m, EqE ((frame ns swap left right).eval (.unary f a)) (.ternary .penc k r m)) ∨
    (∃ k r m c, EqE ((frame ns swap left right).eval (.unary f a)) (.spk k r m c)) := by
  obtain ⟨i, k, hk, rfl, hf⟩ := h
  rcases hf with rfl | ⟨rfl, htail⟩
  · have hi : k < (ballotFields ns i (choice swap left right i).value).length := by
      simpa only [ballot_fields_length] using hk
    have hv : EqE ((frame ns swap left right).eval ((Term.var i.succ).project k))
        (ballotFields ns i (choice swap left right i).value)[k] := by
      simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle, ballot] using
        project_tuple_get (ballotFields ns i (choice swap left right i).value) k hi
    rcases ballot_field_cases ns i (choice swap left right i).value k hi with
      ⟨j, _, hj⟩ | ⟨j, _, hj⟩ | ⟨_, hj⟩
    · rw [hj] at hv
      exact Or.inr (Or.inl ⟨_, _, _, hv⟩)
    · rw [hj] at hv
      exact Or.inr (Or.inr ⟨_, _, _, _, hv⟩)
    · rw [hj] at hv
      exact Or.inr (Or.inr ⟨_, _, _, _, hv⟩)
  · rw [← Term.drop_succ_outer]
    exact Or.inl (ballot_tail_pair_value ns swap left right i (k + 1) htail)

end ExplainableCrypto.Helios.Symbolic.Historical.General
