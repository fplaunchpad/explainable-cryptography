import ExplainableCrypto.Helios.Symbolic.StaticEquivalenceSPOT

namespace ExplainableCrypto.Helios.Symbolic.PublicReconstructionSPOT
open Historical
abbrev names := BallotValueSPOT.names
abbrev vote : CandidateSubstitution 0 Empty := StaticEquivalenceSPOT.singleOne
abbrev world (swap : Bool) := General.frame names swap vote vote
abbrev recipe : Recipe 3 := constructorBallot (.var 0) (fun _ : Fin 1 => .name 40)
  (fun _ => .const .zero) (fun _ : Fin 2 => BallotValueSPOT.proofRecipe)
abbrev boardRecipes : List (Recipe 3) := [.var 1, .var 2]

/-- The new positive fixture uses the public-key handle, not the literal secret name. -/
theorem recipe_public : recipe.Public names.restricted := by
  apply constructorBallot_public
  · trivial
  · intro j; change 40 ∉ names.restricted; decide
  · intro j; trivial
  · intro j
    change True ∧ 40 ∉ names.restricted ∧ True ∧ (True ∧ 40 ∉ names.restricted ∧ True)
    decide

private theorem same_votes_staticEq : (world false).StaticEq (world true) := by
  apply Frame.staticEq_of_pointwise
  intro i
  fin_cases i <;> exact .refl _

private theorem input_accepts : Accepted 0 (publicKey names) BallotValueSPOT.board ((world false).eval recipe) :=
  BallotValueSPOT.abstention_after_both_honest

private theorem honest_board : ∀ i : Fin 2, General.ballot names i (General.choice false vote vote i).value ∈ BallotValueSPOT.board := by
  intro i
  fin_cases i <;> simp [BallotValueSPOT.board, General.choice, vote, StaticEquivalenceSPOT.singleOne,
    BitCandidate.substitution, General.selected_ballot_specialization]

/-- One shared fully public witness reconstructs an accepted fresh abstention
in both identical-vote worlds, recovering the independently fixed nonce and bit. -/
theorem shared_public_reconstruction :
    ∃ (nonces : Fin 1 → Recipe 3) (bits : Fin 1 → Constant) (proofs : Fin 2 → Recipe 3),
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public names.restricted ∧
      (∀ swap : Bool, EqE ((world swap).eval (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs))
        BallotValueSPOT.abstention) ∧
      (∀ swap : Bool, EqE ((world swap).eval (nonces 0)) (.name 40)) ∧ bits 0 = .zero := by
  obtain ⟨nonces, bits, proofs, hb, hc, _, _, hp, he⟩ :=
    General.accepted_ballot_common_constructor names vote vote same_votes_staticEq recipe recipe_public
      BallotValueSPOT.board input_accepts honest_board
  have values (swap : Bool) : EqE (.name 40 : Ground) ((world swap).eval (nonces 0)) ∧
      EqE (Term.const .zero : Ground) (.const (bits 0)) := by
    have hproj := (constructorBallot_project_ciphertext (Term.var 0) nonces (fun j => .const (bits j)) proofs 0).subst
      (world swap).value
    simp only [Term.subst_project] at hproj
    have heval : (world swap).eval recipe = BallotValueSPOT.abstention := rfl
    have hs := he swap
    rw [heval] at hs
    have hcipher := (project_tuple_get BallotValueSPOT.zeroFields 0 (by decide)).symm.trans
      ((EqE.unary .fst hs).trans hproj)
    exact (EqE.penc_iff _ _ _ _ _ _).mp hcipher |>.2
  refine ⟨nonces, bits, proofs, hc, hp, ?_, fun swap => (values swap).1.symm, ?_⟩
  · intro swap
    exact (he swap).symm
  · rcases hb 0 with hz | ho
    · exact hz
    · exact False.elim (zero_not_one (ho ▸ (values false).2))

/-- Acceptance transfer is instantiated on a nonempty public board and an
accepted fresh ballot; replay is rejected in both worlds by actual weeding. -/
theorem acceptance_transfer_and_replay :
    (∀ swap : Bool, Accepted 0 ((world swap).eval (.var 0))
      (boardRecipes.map (world swap).eval) ((world swap).eval recipe)) ∧
    ∀ swap : Bool, ¬ Accepted 0 ((world swap).eval (.var 0))
      (boardRecipes.map (world swap).eval) ((world swap).eval (.var 1)) := by
  have hboard : ∀ r ∈ boardRecipes, r.Public names.restricted := by
    intro r hr
    simp only [boardRecipes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> trivial
  constructor
  · intro swap
    cases swap with
    | false => exact input_accepts
    | true => exact (same_votes_staticEq.accepted_iff 0 (.var 0) recipe boardRecipes trivial recipe_public hboard).mp input_accepts
  · intro swap
    exact accepted_excludes_replay _ _ _ _ (by simp [boardRecipes])

end ExplainableCrypto.Helios.Symbolic.PublicReconstructionSPOT
