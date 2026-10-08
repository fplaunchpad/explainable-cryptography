import ExplainableCrypto.Helios.Symbolic.AcceptedBallotReconstruction
import ExplainableCrypto.Helios.Symbolic.BallotValueSPOT

namespace ExplainableCrypto.Helios.Symbolic.AcceptedReconstructionSPOT
open Historical

abbrev pairNonce : Ground := .binary .compose (.name 20) (.name 20)
abbrev hiddenPair : Ground := .unary .fst (.binary .pair pairNonce (.const .bottom))

/-- Permanent minimized gate failure: a non-normal target hides two factors. -/
theorem normal_target_required : EqE pairNonce hiddenPair ∧
    pairNonce.composeFactors.card = 2 ∧ hiddenPair.composeFactors.card = 1 ∧ ¬ Irreducible hiddenPair := by
  refine ⟨(RootStep.fst pairNonce (.const .bottom)).sound.symm, rfl, rfl, ?_⟩
  intro hi
  exact hi pairNonce (RootStep.fst pairNonce (.const .bottom)).to_modulo

/-- At one candidate there are no other factors to make the inequality strict. -/
theorem single_candidate_count_boundary :
    EqE (foldCandidates (n := 0) .compose (fun _ => (Term.name 20 : Ground))) (.name 20) ∧
    (foldCandidates (n := 0) .compose (fun _ => (Term.name 20 : Ground))).composeFactors.card = 1 :=
  ⟨.refl _, rfl⟩

theorem repeated_nonce_aggregate_too_large :
    ¬ EqE (foldCandidates (n := 1) .compose (fun j => if j = 0 then pairNonce else hiddenPair)) pairNonce := by
  apply nonce_fold_not_eq_small_normal (by decide) _ 0 (fun _ => 20) (.refl _)
  · exact named_nonce_fold_irreducible (fun _ : Fin 2 => 20)
  · exact Nat.le_refl _

abbrev names : Names 1 := HistoricalFrameSPOT.names
abbrev freshNames : Names 1 := ⟨10, 11, fun _ j => 40 + j.val⟩
abbrev board (swap : Bool) : List Ground :=
  [ballot names 0 (choice swap 0 1 0), ballot names 1 (choice swap 0 1 1)]

private theorem board_contains (swap : Bool) :
    ∀ i : Fin 2, ballot names i (choice swap 0 1 i) ∈ board swap := by
  intro i
  fin_cases i <;> simp [board]

abbrev freshRecipe (chosen : Fin 2) : Recipe 3 :=
  (ballot freshNames 0 chosen).subst (fun x : Empty => x.elim)

private theorem fresh_eval (swap : Bool) (chosen : Fin 2) :
    (frame names swap 0 1).eval (freshRecipe chosen) = ballot freshNames 0 chosen := by
  simp only [Frame.eval, freshRecipe, Term.subst_subst]
  have hf : (fun x : Empty => (Empty.elim x : Recipe 3).subst (frame names swap 0 1).value) =
      (Term.var : Empty → Ground) := by funext x; exact x.elim
  rw [hf, Term.subst_var]

private theorem fresh_public (chosen : Fin 2) : (freshRecipe chosen).Public names.nonceNames := by
  fin_cases chosen <;>
    simp [freshRecipe, ballot, ballotFields, ciphertext, componentProof, aggregateProof,
      foldCandidates, publicKey, vote, Term.tuple, Term.subst, Term.Public, freshNames,
      List.finRange_succ] <;> decide

private theorem fresh_accepts (swap : Bool) (chosen : Fin 2) :
    Accepted 1 (publicKey names) (board swap) (ballot freshNames 0 chosen) := by
  refine ⟨honest_proofs_valid freshNames 0 chosen, ballot_tail_guard freshNames 0 chosen, ?_⟩
  intro earlier hm i j he
  have exclude (v : Fin 2) (hv : EqE ((ballot names v (choice swap 0 1 v)).project i.val)
      ((ballot freshNames 0 chosen).project j.val)) : False := by
    have hc := (ballot_project_ciphertext names v (choice swap 0 1 v) i).symm.trans
      (hv.trans (ballot_project_ciphertext freshNames 0 chosen j))
    have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
    change 20 + 2 * v.val + i.val = 40 + j.val at hn
    have hi := i.isLt
    have hj := j.isLt
    have hv := v.isLt
    omega
  simp only [board, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact exclude 0 he
  · have hm' : earlier = ballot names 1 (choice swap 0 1 1) := by simpa using hm
    subst earlier
    exact exclude 1 he

/-- Both choices and swapped worlds instantiate the reconstruction theorem for the encoded frames. Exact
nonce and bit values are recovered independently from the literal fresh ballot. -/
theorem fresh_two_candidate_reconstruction (swap : Bool) (chosen : Fin 2) :
    ∃ (nonces : Fin 2 → Recipe 3) (bits : Fin 2 → Constant) (proofs : Fin 3 → Recipe 3),
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public names.nonceNames ∧
      EqE ((frame names swap 0 1).eval (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs))
        (ballot freshNames 0 chosen) ∧
      ∀ j, EqE ((frame names swap 0 1).eval (nonces j)) (.name (40 + j.val)) ∧
        EqE (Term.const (bits j) : Ground) (vote chosen j) := by
  have ha : Accepted 1 (publicKey names) (board swap) ((frame names swap 0 1).eval (freshRecipe chosen)) := by
    rw [fresh_eval]
    exact fresh_accepts swap chosen
  obtain ⟨nonces, bits, proofs, _, hbits, _, _, hpub, he⟩ :=
    accepted_ballot_constructor_recipe names swap 0 1 (freshRecipe chosen) (fresh_public chosen)
      (board swap) ha (board_contains swap)
  rw [fresh_eval] at he
  refine ⟨nonces, bits, proofs, hbits, hpub, he.symm, ?_⟩
  intro j
  have hp := (constructorBallot_project_ciphertext (Term.var 0) nonces (fun j => .const (bits j)) proofs j).subst
    (frame names swap 0 1).value
  simp only [Term.subst_project] at hp
  have hc : EqE (.ternary .penc (publicKey names) ((frame names swap 0 1).eval (nonces j)) (.const (bits j)))
      (ciphertext freshNames 0 chosen j) := by
    have heproj := EqE.unary .fst (he.symm.drop j.val)
    exact hp.symm.trans (heproj.trans (ballot_project_ciphertext freshNames 0 chosen j))
  have hf := (EqE.penc_iff _ _ _ _ _ _).mp hc
  exact ⟨hf.2.1, hf.2.2⟩

/-- Reconstruction also covers an adversarial abstention after one-hot honest ballots. -/
theorem abstention_reconstruction :
    ∃ (nonces : Fin 1 → Recipe 3) (bits : Fin 1 → Constant) (proofs : Fin 2 → Recipe 3),
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public BallotValueSPOT.names.nonceNames ∧
      EqE BallotValueSPOT.abstention ((frame BallotValueSPOT.names false 0 0).eval
        (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs)) := by
  let r := constructorBallot (.var 0) (fun _ : Fin 1 => (Term.name 40 : Recipe 3))
    (fun _ => .const .zero) (fun _ : Fin 2 => BallotValueSPOT.proofRecipe)
  have hp : r.Public BallotValueSPOT.names.nonceNames := by
    apply constructorBallot_public
    · trivial
    · intro j; change 40 ∉ BallotValueSPOT.names.nonceNames; decide
    · intro j; trivial
    · intro j
      change True ∧ 40 ∉ BallotValueSPOT.names.nonceNames ∧ True ∧
        (True ∧ 40 ∉ BallotValueSPOT.names.nonceNames ∧ True)
      decide
  have heval : (frame BallotValueSPOT.names false 0 0).eval r = BallotValueSPOT.abstention := rfl
  have ha : Accepted 0 (publicKey BallotValueSPOT.names) BallotValueSPOT.board
      ((frame BallotValueSPOT.names false 0 0).eval r) := by
    rw [heval]
    exact BallotValueSPOT.abstention_after_both_honest
  have hb : ∀ i : Fin 2, ballot BallotValueSPOT.names i (choice false 0 0 i) ∈ BallotValueSPOT.board := by
    intro i; fin_cases i <;> simp [BallotValueSPOT.board, choice]
  obtain ⟨nonces, bits, proofs, _, hc, _, _, hpub, he⟩ :=
    accepted_ballot_constructor_recipe BallotValueSPOT.names false 0 0 r hp BallotValueSPOT.board ha hb
  exact ⟨nonces, bits, proofs, hc, hpub, he⟩

/-- The source permits honest abstention; the current selected-index frame
family cannot represent this accepted ballot, even up to full E. -/
theorem honest_abstention_scope_gap (i : Fin 2) (chosen : Fin 1) :
    Accepted 0 BallotValueSPOT.key [] BallotValueSPOT.abstention ∧
      ¬ EqE BallotValueSPOT.abstention (ballot BallotValueSPOT.names i chosen) := by
  refine ⟨BallotValueSPOT.abstention_accepted, ?_⟩
  intro he
  fin_cases chosen
  have hc := (project_tuple_get BallotValueSPOT.zeroFields 0 (by decide)).symm.trans
    ((EqE.unary .fst he).trans (ballot_project_ciphertext BallotValueSPOT.names i 0 0))
  exact zero_not_one ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.2

/-- Without the required board members, an honest one-candidate ballot accepts
and its component proof is the same value as its aggregate proof. -/
theorem board_membership_required :
    (Term.var 1 : Recipe 3).Public BallotValueSPOT.names.nonceNames ∧
    Accepted 0 (publicKey BallotValueSPOT.names) []
      ((frame BallotValueSPOT.names false 0 0).eval (.var 1)) ∧
    EqE (((frame BallotValueSPOT.names false 0 0).eval (.var 1)).project 1)
      (aggregateProof BallotValueSPOT.names 0 0) :=
  ⟨trivial, honest_empty_board_accepts _ _ _, ballot_project_proof _ _ _ 0⟩

/-- Literal hidden nonces produce the forbidden value if recipe publicness is removed. -/
theorem public_nonce_premise_required :
    ¬ (Term.binary .compose (.name 20) (.name 21) : Recipe 3).Public names.nonceNames ∧
    EqE ((frame names false 0 1).eval (.binary .compose (.name 20) (.name 21)))
      (foldCandidates .compose (fun j => .name (names.nonce 0 j))) := by
  constructor
  · change ¬ (20 ∉ names.nonceNames ∧ 21 ∉ names.nonceNames)
    decide
  · exact .refl _

abbrev copiedCipher : Recipe 3 := .binary .mul ((Term.var 1).project 0) ((Term.var 1).project 1)
abbrev freshZero : Recipe 3 := .ternary .penc (.var 0) (.name 40) (.const .zero)
abbrev copiedProof : Recipe 3 := (Term.var 1).project 4
abbrev freshZeroProof : Recipe 3 := .spk (.var 0) (.name 40) (.const .zero) freshZero
abbrev attackFields : List (Recipe 3) := [copiedCipher, freshZero, copiedProof, freshZeroProof, copiedProof]
abbrev attack : Recipe 3 := Term.tuple attackFields

private theorem attack_public : attack.Public names.nonceNames := by
  simp [attack, copiedCipher, freshZero, copiedProof, freshZeroProof,
    Term.tuple, Term.Public, Term.project, Term.drop]
  decide

private theorem attack_field (swap : Bool) (index : Nat) (hi : index < attackFields.length) :
    EqE (((frame names swap 0 1).eval attack).project index)
      ((attackFields[index]).subst (frame names swap 0 1).value) := by
  simpa only [Frame.eval, Term.subst_project] using
    (project_tuple_get attackFields index hi).subst (frame names swap 0 1).value

private theorem copied_values (swap : Bool) :
    EqE ((frame names swap 0 1).eval copiedCipher)
      (.ternary .penc (publicKey names) (.binary .compose (.name 20) (.name 21)) (.const .one)) ∧
    EqE ((frame names swap 0 1).eval copiedProof)
      (.spk (publicKey names) (.binary .compose (.name 20) (.name 21)) (.const .one)
        ((frame names swap 0 1).eval copiedCipher)) := by
  have hc : EqE ((frame names swap 0 1).eval copiedCipher)
      (foldCandidates .mul (ciphertext names 0 (choice swap 0 1 0))) :=
    .binary .mul (ballot_project_ciphertext names 0 (choice swap 0 1 0) 0)
      (ballot_project_ciphertext names 0 (choice swap 0 1 0) 1)
  exact ⟨hc.trans (ciphertext_product names 0 (choice swap 0 1 0)),
    (ballot_project_aggregate names 0 (choice swap 0 1 0)).trans
      (.spk (.refl _) (.refl _) (vote_sum_one (choice swap 0 1 0)).sound hc.symm)⟩

theorem copied_aggregate_component_checks (swap : Bool) : ∀ j : Fin 2,
    EqE (.ternary .checkspk (publicKey names) (((frame names swap 0 1).eval attack).project j.val)
      (((frame names swap 0 1).eval attack).project (2 + j.val))) (.const .ok) := by
  intro j
  fin_cases j
  · have hv := copied_values swap
    exact (EqE.ternary .checkspk (.refl _) (attack_field swap 0 (by decide))
      (attack_field swap 2 (by decide))).trans
      ((EqE.check_ok_iff_components _ _ _).mpr ⟨_, .one, Or.inr rfl, hv.1, hv.2⟩)
  · exact (EqE.ternary .checkspk (.refl _) (attack_field swap 1 (by decide))
      (attack_field swap 3 (by decide))).trans (RootStep.check_zero (publicKey names) (.name 40)).sound

private theorem attack_tail (swap : Bool) : TailGuard 1 ((frame names swap 0 1).eval attack) := by
  have h := (drop_tuple attackFields).subst (frame names swap 0 1).value
  rw [Term.subst_drop] at h
  exact h

private theorem attack_no_reuse (swap : Bool) : NoReuse 1 (board swap) ((frame names swap 0 1).eval attack) := by
  intro earlier hm i j he
  have exclude (v : Fin 2) (he : EqE ((ballot names v (choice swap 0 1 v)).project i.val)
      (((frame names swap 0 1).eval attack).project j.val)) : False := by
    have hc := (ballot_project_ciphertext names v (choice swap 0 1 v) i).symm.trans he
    fin_cases j
    · have hn := ((EqE.penc_iff _ _ _ _ _ _).mp
        (hc.trans ((attack_field swap 0 (by decide)).trans (copied_values swap).1))).2.1
      have hcount := hn.symm.compose_card_le_of_irreducible (name_irreducible _)
      change 2 ≤ 1 at hcount
      omega
    · have hn := (EqE.name_iff _ _).mp ((EqE.penc_iff _ _ _ _ _ _).mp
        (hc.trans (attack_field swap 1 (by decide)))).2.1
      change 20 + 2 * v.val + i.val = 40 at hn
      have hv := v.isLt
      have hi := i.isLt
      omega
  simp only [board, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact exclude 0 he
  · have hm' : earlier = ballot names 1 (choice swap 0 1 1) := by simpa using hm
    subst earlier
    exact exclude 1 he

/-- The copied aggregate passes both component checks, tail and weeding. The
remaining aggregate check must fail, as the general exclusion theorem proves. -/
theorem copied_aggregate_fails_aggregate_check (swap : Bool) :
    TailGuard 1 ((frame names swap 0 1).eval attack) ∧
    NoReuse 1 (board swap) ((frame names swap 0 1).eval attack) ∧
    ¬ ProofValid 1 (publicKey names) ((frame names swap 0 1).eval attack) := by
  refine ⟨attack_tail swap, attack_no_reuse swap, ?_⟩
  intro hv
  apply accepted_component_not_honest_aggregate names swap 0 1 attack attack_public
    (board swap) ⟨hv, attack_tail swap, attack_no_reuse swap⟩ (board_contains swap) 0 0
  exact (attack_field swap 2 (by decide)).trans (ballot_project_aggregate names 0 (choice swap 0 1 0))

end ExplainableCrypto.Helios.Symbolic.AcceptedReconstructionSPOT
