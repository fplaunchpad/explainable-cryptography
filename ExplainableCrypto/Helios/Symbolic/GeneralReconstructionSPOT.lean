import ExplainableCrypto.Helios.Symbolic.GeneralAcceptedReconstruction
import ExplainableCrypto.Helios.Symbolic.GeneralCandidateSPOT
import ExplainableCrypto.Helios.Symbolic.AcceptedReconstructionSPOT

namespace ExplainableCrypto.Helios.Symbolic.GeneralReconstructionSPOT
open Historical

abbrev names : Names 1 := HistoricalFrameSPOT.names
abbrev freshNames : Names 1 := AcceptedReconstructionSPOT.freshNames
abbrev board (swap : Bool) (left right : CandidateSubstitution 1 Empty) : List Ground :=
  [General.ballot names 0 (General.choice swap left right 0).value,
    General.ballot names 1 (General.choice swap left right 1).value]

private theorem board_contains (swap : Bool) (left right : CandidateSubstitution 1 Empty) :
    ∀ i : Fin 2, General.ballot names i (General.choice swap left right i).value ∈ board swap left right := by
  intro i
  fin_cases i <;> simp [board]

private theorem fresh_eval (swap : Bool) (left right : CandidateSubstitution 1 Empty) (chosen : Fin 2) :
    (General.frame names swap left right).eval (AcceptedReconstructionSPOT.freshRecipe chosen) =
      Historical.ballot freshNames 0 chosen := by
  simp only [Frame.eval, AcceptedReconstructionSPOT.freshRecipe, Term.subst_subst]
  have hf : (fun x : Empty => (Empty.elim x : Recipe 3).subst (General.frame names swap left right).value) =
      (Term.var : Empty → Ground) := by funext x; exact x.elim
  rw [hf, Term.subst_var]

private theorem fresh_public (chosen : Fin 2) :
    (AcceptedReconstructionSPOT.freshRecipe chosen).Public names.nonceNames := by
  fin_cases chosen <;>
    simp [AcceptedReconstructionSPOT.freshRecipe, Historical.ballot, Historical.ballotFields,
      Historical.ciphertext, Historical.componentProof, Historical.aggregateProof, foldCandidates,
      publicKey, vote, Term.tuple, Term.subst, Term.Public,
      AcceptedReconstructionSPOT.freshNames, List.finRange_succ] <;> decide

private theorem fresh_accepts (swap : Bool) (left right : CandidateSubstitution 1 Empty) (chosen : Fin 2) :
    Accepted 1 (publicKey names) (board swap left right) (Historical.ballot freshNames 0 chosen) := by
  refine ⟨Historical.honest_proofs_valid freshNames 0 chosen, Historical.ballot_tail_guard freshNames 0 chosen, ?_⟩
  intro earlier hm i j he
  have exclude (v : Fin 2) (hv : EqE ((General.ballot names v (General.choice swap left right v).value).project i.val)
      ((Historical.ballot freshNames 0 chosen).project j.val)) : False := by
    have hc := (General.ballot_project_ciphertext names v (General.choice swap left right v).value i).symm.trans
      (hv.trans (Historical.ballot_project_ciphertext freshNames 0 chosen j))
    have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
    change 20 + 2 * v.val + i.val = 40 + j.val at hn
    have hi := i.isLt
    have hj := j.isLt
    have hv := v.isLt
    omega
  simp only [board, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact exclude 0 he
  · have hm' : earlier = General.ballot names 1 (General.choice swap left right 1).value := by simpa using hm
    subst earlier
    exact exclude 1 he

/-- The full theorem is instantiated after arbitrary valid honest substitutions,
not only literal one-hot choices. Nonce and bit values are checked independently. -/
theorem fresh_reconstruction_after_general_votes (swap : Bool)
    (left right : CandidateSubstitution 1 Empty) (chosen : Fin 2) :
    ∃ (nonces : Fin 2 → Recipe 3) (bits : Fin 2 → Constant) (proofs : Fin 3 → Recipe 3),
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public names.nonceNames ∧
      EqE ((General.frame names swap left right).eval
        (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs)) (Historical.ballot freshNames 0 chosen) ∧
      ∀ j, EqE ((General.frame names swap left right).eval (nonces j)) (.name (40 + j.val)) ∧
        EqE (Term.const (bits j) : Ground) (vote chosen j) := by
  have ha : Accepted 1 (publicKey names) (board swap left right)
      ((General.frame names swap left right).eval (AcceptedReconstructionSPOT.freshRecipe chosen)) := by
    rw [fresh_eval]
    exact fresh_accepts swap left right chosen
  obtain ⟨nonces, bits, proofs, _, hbits, _, _, hpub, he⟩ :=
    General.accepted_ballot_constructor_recipe names swap left right (AcceptedReconstructionSPOT.freshRecipe chosen)
      (fresh_public chosen) (board swap left right) ha (board_contains swap left right)
  rw [fresh_eval] at he
  refine ⟨nonces, bits, proofs, hbits, hpub, he.symm, ?_⟩
  intro j
  have hp := (constructorBallot_project_ciphertext (Term.var 0) nonces (fun j => .const (bits j)) proofs j).subst
    (General.frame names swap left right).value
  simp only [Term.subst_project] at hp
  have hc : EqE (.ternary .penc (publicKey names) ((General.frame names swap left right).eval (nonces j)) (.const (bits j)))
      (Historical.ciphertext freshNames 0 chosen j) := by
    have heproj := EqE.unary .fst (he.symm.drop j.val)
    exact hp.symm.trans (heproj.trans (Historical.ballot_project_ciphertext freshNames 0 chosen j))
  have hf := (EqE.penc_iff _ _ _ _ _ _).mp hc
  exact ⟨hf.2.1, hf.2.2⟩

/-- Honest and adversarial abstention coexist. The full reconstruction returns
zero, with actual nonce weeding against both earlier all-zero ballots. -/
theorem all_abstentions_reconstruction :
    let ns := BallotValueSPOT.names
    let c : CandidateSubstitution 0 Empty := (BitCandidate.abstain 0).substitution
    ∃ (nonces : Fin 1 → Recipe 3) (bits : Fin 1 → Constant) (proofs : Fin 2 → Recipe 3),
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public ns.nonceNames ∧
      EqE BallotValueSPOT.abstention ((General.frame ns false c c).eval
        (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs)) ∧ bits 0 = .zero := by
  dsimp only
  let ns := BallotValueSPOT.names
  let c : CandidateSubstitution 0 Empty := (BitCandidate.abstain 0).substitution
  let earlier := [General.ballot ns 0 c.value, General.ballot ns 1 c.value]
  let r := constructorBallot (.var 0) (fun _ : Fin 1 => (Term.name 40 : Recipe 3))
    (fun _ => .const .zero) (fun _ : Fin 2 => BallotValueSPOT.proofRecipe)
  have hp : r.Public ns.nonceNames := by
    apply constructorBallot_public
    · trivial
    · intro j; change 40 ∉ ns.nonceNames; decide
    · intro j; trivial
    · intro j
      change True ∧ 40 ∉ ns.nonceNames ∧ True ∧ (True ∧ 40 ∉ ns.nonceNames ∧ True)
      decide
  have heval : (General.frame ns false c c).eval r = BallotValueSPOT.abstention := rfl
  have ha : Accepted 0 (publicKey ns) earlier ((General.frame ns false c c).eval r) := by
    rw [heval]
    refine ⟨BallotValueSPOT.abstention_accepted.1, BallotValueSPOT.abstention_accepted.2.1, ?_⟩
    intro previous hm i j he
    fin_cases i
    fin_cases j
    have exclude (v : Fin 2) (he : EqE ((General.ballot ns v c.value).project 0) (BallotValueSPOT.abstention.project 0)) : False := by
      have hc := (General.ballot_project_ciphertext ns v c.value 0).symm.trans
        (he.trans (project_tuple_get BallotValueSPOT.zeroFields 0 (by decide)))
      have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
      change 20 + v.val = 40 at hn
      have hv := v.isLt
      omega
    simp only [earlier, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact exclude 0 he
    · have hm' : previous = General.ballot ns 1 c.value := by simpa using hm
      subst previous
      exact exclude 1 he
  have hboard : ∀ i : Fin 2, General.ballot ns i (General.choice false c c i).value ∈ earlier := by
    intro i; fin_cases i <;> simp [earlier, General.choice]
  obtain ⟨nonces, bits, proofs, hbits, hc, _, _, hpub, he⟩ :=
    General.accepted_ballot_constructor_recipe ns false c c r hp earlier ha hboard
  rw [heval] at he
  refine ⟨nonces, bits, proofs, hc, hpub, he, ?_⟩
  have hproj := (constructorBallot_project_ciphertext (Term.var 0) nonces (fun j => .const (bits j)) proofs 0).subst
    (General.frame ns false c c).value
  simp only [Term.subst_project] at hproj
  have hcipher := (project_tuple_get BallotValueSPOT.zeroFields 0 (by decide)).symm.trans
    ((EqE.unary .fst he).trans hproj)
  have hbit := ((EqE.penc_iff _ _ _ _ _ _).mp hcipher).2.2
  rcases hbits 0 with hz | ho
  · exact hz
  · rw [ho] at hbit
    exact False.elim (zero_not_one hbit)

abbrev attack : Recipe 3 := AcceptedReconstructionSPOT.attack
abbrev attackFields : List (Recipe 3) := AcceptedReconstructionSPOT.attackFields

private theorem attack_public : attack.Public names.nonceNames := by
  simp [attack, AcceptedReconstructionSPOT.attack, AcceptedReconstructionSPOT.copiedCipher,
    AcceptedReconstructionSPOT.freshZero, AcceptedReconstructionSPOT.copiedProof,
    AcceptedReconstructionSPOT.freshZeroProof, Term.tuple, Term.Public, Term.project, Term.drop]
  decide

private theorem attack_field (swap : Bool) (left right : CandidateSubstitution 1 Empty)
    (index : Nat) (hi : index < attackFields.length) :
    EqE (((General.frame names swap left right).eval attack).project index)
      ((attackFields[index]).subst (General.frame names swap left right).value) := by
  simpa only [Frame.eval, Term.subst_project] using
    (project_tuple_get attackFields index hi).subst (General.frame names swap left right).value

/-- Borrowing an honest aggregate passes the component checks for abstaining
and nonliteral honest votes too. -/
theorem copied_aggregate_component_checks (swap : Bool) (left right : CandidateSubstitution 1 Empty) : ∀ j : Fin 2,
    EqE (.ternary .checkspk (publicKey names) (((General.frame names swap left right).eval attack).project j.val)
      (((General.frame names swap left right).eval attack).project (2 + j.val))) (.const .ok) := by
  intro j
  fin_cases j
  · exact (EqE.ternary .checkspk (.refl _) (attack_field swap left right 0 (by decide))
      (attack_field swap left right 2 (by decide))).trans
      (General.honest_proofs_valid names 0 (General.choice swap left right 0).value
        (General.choice swap left right 0).valid).1
  · exact (EqE.ternary .checkspk (.refl _) (attack_field swap left right 1 (by decide))
      (attack_field swap left right 3 (by decide))).trans (RootStep.check_zero (publicKey names) (.name 40)).sound

private theorem attack_tail (swap : Bool) (left right : CandidateSubstitution 1 Empty) :
    TailGuard 1 ((General.frame names swap left right).eval attack) := by
  have h := (drop_tuple attackFields).subst (General.frame names swap left right).value
  rw [Term.subst_drop] at h
  exact h

private theorem attack_no_reuse (swap : Bool) (left right : CandidateSubstitution 1 Empty) :
    NoReuse 1 (board swap left right) ((General.frame names swap left right).eval attack) := by
  intro earlier hm i j he
  have hcopy := (General.ballot_aggregate_ciphertext names 0 (General.choice swap left right 0).value).trans
    (foldCandidates_ciphertexts (publicKey names) (fun j => .name (names.nonce 0 j))
      (General.choice swap left right 0).value)
  have exclude (v : Fin 2) (he : EqE ((General.ballot names v (General.choice swap left right v).value).project i.val)
      (((General.frame names swap left right).eval attack).project j.val)) : False := by
    have hc := (General.ballot_project_ciphertext names v (General.choice swap left right v).value i).symm.trans he
    fin_cases j
    · have hn := ((EqE.penc_iff _ _ _ _ _ _).mp
        (hc.trans ((attack_field swap left right 0 (by decide)).trans hcopy))).2.1
      have hcount := hn.symm.compose_card_le_of_irreducible (name_irreducible _)
      change 2 ≤ 1 at hcount
      omega
    · have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp
        (hc.trans (attack_field swap left right 1 (by decide)))).2.1
      change 20 + 2 * v.val + i.val = 40 at hn
      have hv := v.isLt
      have hi := i.isLt
      omega
  simp only [board, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact exclude 0 he
  · have hm' : earlier = General.ballot names 1 (General.choice swap left right 1).value := by simpa using hm
    subst earlier
    exact exclude 1 he

/-- The remaining aggregate check rejects the borrowed proof after all other
checks succeed, uniformly over both honest candidate substitutions and swaps. -/
theorem copied_aggregate_rejected_general (swap : Bool) (left right : CandidateSubstitution 1 Empty) :
    TailGuard 1 ((General.frame names swap left right).eval attack) ∧
    NoReuse 1 (board swap left right) ((General.frame names swap left right).eval attack) ∧
    ¬ ProofValid 1 (publicKey names) ((General.frame names swap left right).eval attack) := by
  refine ⟨attack_tail swap left right, attack_no_reuse swap left right, ?_⟩
  intro hv
  apply General.accepted_component_not_honest_aggregate names swap left right attack attack_public
    (board swap left right) ⟨hv, attack_tail swap left right, attack_no_reuse swap left right⟩
    (board_contains swap left right) 0 0
  exact (attack_field swap left right 2 (by decide)).trans
    (General.ballot_project_aggregate names 0 (General.choice swap left right 0).value)

end ExplainableCrypto.Helios.Symbolic.GeneralReconstructionSPOT
