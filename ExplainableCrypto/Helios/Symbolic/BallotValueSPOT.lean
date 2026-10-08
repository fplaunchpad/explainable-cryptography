import ExplainableCrypto.Helios.Symbolic.BallotTupleValues
import ExplainableCrypto.Helios.Symbolic.HistoricalAcceptedProofs
import ExplainableCrypto.Helios.Symbolic.HistoricalValiditySPOT

namespace ExplainableCrypto.Helios.Symbolic.BallotValueSPOT
open Historical

abbrev key : Ground := .unary .pk (.name 10)
abbrev zeroCipher : Ground := .ternary .penc key (.name 40) (.const .zero)
abbrev zeroProof : Ground := .spk key (.name 40) (.const .zero) zeroCipher
abbrev zeroFields : List Ground := [zeroCipher, zeroProof, zeroProof]
abbrev abstention : Ground := Term.tuple zeroFields

theorem zero_with_any_tail_valid (tail : Ground) :
    ProofValid 0 key (tupleWithTail zeroFields tail) := by
  have hc := project_tupleWithTail_get zeroFields tail 0 (by decide)
  have hp := project_tupleWithTail_get zeroFields tail 1 (by decide)
  have ha := project_tupleWithTail_get zeroFields tail 2 (by decide)
  constructor
  · exact (EqE.ternary .checkspk (.refl _) hc ha).trans
      (RootStep.check_zero key (.name 40)).sound
  · intro j
    fin_cases j
    exact (EqE.ternary .checkspk (.refl _) hc hp).trans
      (RootStep.check_zero key (.name 40)).sound

/-- Definition 4 allows an accepted all-zero ballot. -/
theorem abstention_accepted : Accepted 0 key [] abstention := by
  refine ⟨zero_with_any_tail_valid (.const .bottom), drop_tuple zeroFields, ?_⟩
  intro earlier h
  simp at h

theorem abstention_values : Nonempty (BallotValues 0 key abstention) :=
  (proofValid_iff_values key abstention).mp abstention_accepted.1

theorem abstention_tuple_reconstructed :
    EqE abstention (Term.tuple ((List.range 3).map (fun i => abstention.project i))) :=
  abstention_accepted.1.tuple_value abstention_accepted.2.1

/-- Permanent kernel control for the minimized exactly-one PBT failure. -/
theorem exactly_one_strengthening_false :
    CandidateValues (V := Empty) (n := 0) (fun _ => .const .zero) ∧
      ¬ EqE (foldCandidates (n := 0) .add (fun _ => (Term.const .zero : Ground))) (.const .one) :=
  ⟨Or.inl (.refl _), zero_not_one⟩

theorem two_candidate_abstention_sum :
    CandidateValues (V := Empty) (n := 1) (fun _ => .const .zero) :=
  Or.inl (.equation .zero_zero)

/-- The checks do not enforce the tail; the acceptance predicate must retain it. -/
theorem non_bottom_tail_rejected :
    ProofValid 0 key (tupleWithTail zeroFields (.name 41)) ∧
      ¬ Accepted 0 key [] (tupleWithTail zeroFields (.name 41)) := by
  refine ⟨zero_with_any_tail_valid _, ?_⟩
  intro ha
  have he := (drop_tupleWithTail zeroFields (.name 41)).symm.trans ha.2.1
  have hn := he.denote (fun _ => 0) (fun _ => 0)
  simp [Term.denote] at hn

theorem pair_value_premise_required :
    ¬ EqE (Term.name 40 : Ground)
      (.binary .pair (.unary .fst (.name 40)) (.unary .snd (.name 40))) := by
  intro he
  cases (name_irreducible 40).pair_head_of_eq he

abbrev oneCipher (r : Nat) : Ground := .ternary .penc key (.name r) (.const .one)
abbrev oneProof (r : Nat) : Ground := .spk key (.name r) (.const .one) (oneCipher r)
abbrev twoOneFields : List Ground :=
  [oneCipher 40, oneCipher 41, oneProof 40, oneProof 41,
    .spk key (.binary .compose (.name 40) (.name 41)) (.const .one)
      (.binary .mul (oneCipher 40) (oneCipher 41))]
abbrev twoOnes : Ground := Term.tuple twoOneFields

private theorem twoOne_cipher (j : Fin 2) :
    EqE (twoOnes.project j.val) (.ternary .penc key (.name (40 + j.val)) (.const .one)) := by
  fin_cases j
  · exact project_tuple_get twoOneFields 0 (by decide)
  · exact project_tuple_get twoOneFields 1 (by decide)

/-- Both component checks succeed, so the aggregate check is load-bearing. -/
theorem two_ones_component_checks : ∀ j : Fin 2,
    EqE (.ternary .checkspk key (twoOnes.project j.val) (twoOnes.project (2 + j.val))) (.const .ok) := by
  intro j
  fin_cases j
  · exact (EqE.ternary .checkspk (.refl _) (twoOne_cipher 0)
      (project_tuple_get twoOneFields 2 (by decide))).trans (RootStep.check_one key (.name 40)).sound
  · exact (EqE.ternary .checkspk (.refl _) (twoOne_cipher 1)
      (project_tuple_get twoOneFields 3 (by decide))).trans (RootStep.check_one key (.name 41)).sound

theorem two_ones_invalid : ¬ ProofValid 1 key twoOnes := by
  intro h
  have hc := h.candidate_of_ciphertexts (fun j => .name (40 + j.val))
    (fun _ => .const .one) twoOne_cipher
  rcases hc with hz | ho
  · have hd := hz.denote (fun _ => 0) (fun _ => 0)
    change 1 + 1 = 0 at hd
    omega
  · exact two_not_one ho

/-- Copying a proof to a fresh ciphertext fails even with an unchanged vote. -/
theorem copied_proof_rebinding_rejected :
    ¬ EqE (.ternary .checkspk key (oneCipher 41) (oneProof 40)) (.const .ok) := by
  intro h
  have he := successful_checks_same_proof (RootStep.check_one key (.name 40)).sound h (.refl _)
  have hr := ((EqE.penc_iff _ _ _ _ _ _).mp he).2.1
  have hn := (EqE.name_iff _ _).mp hr
  omega

theorem fresh_honest_proofs_cannot_be_reused (swap : Bool) (i j : Fin 2) :
    ¬ EqE ((ballot HistoricalFrameSPOT.names 0 (choice swap 0 1 0)).project (2 + i.val))
      ((ballot HistoricalFrameSPOT.names 1 (choice swap 0 1 1)).project (2 + j.val)) :=
  accepted_component_proof_not_reused (HistoricalValiditySPOT.fresh_second_ballot_accepts swap)
    (by simp) (honest_proofs_valid _ _ _) i j

/-- Validity and the guard permit replay; the board's weeding condition rejects it. -/
theorem weeding_is_required : ProofValid 0 key abstention ∧ TailGuard 0 abstention ∧
    EqE (abstention.project 1) (abstention.project 1) ∧
    ¬ Accepted 0 key [abstention] abstention :=
  ⟨abstention_accepted.1, abstention_accepted.2.1, .refl _,
    accepted_excludes_replay _ _ _ _ (by simp)⟩

abbrev names : Names 0 := ⟨10, 11, fun i _ => 20 + i.val⟩
abbrev board : List Ground := [ballot names 0 0, ballot names 1 0]

/-- Nonvacuous input for the historical minimum-proof theorem: both honest
ballots are present and a fresh all-zero adversarial ballot is accepted. -/
theorem abstention_after_both_honest : Accepted 0 (publicKey names) board abstention := by
  refine ⟨abstention_accepted.1, abstention_accepted.2.1, ?_⟩
  intro earlier hm i j he
  fin_cases i
  fin_cases j
  have exclude (v : Fin 2) (he : EqE ((ballot names v 0).project 0) (abstention.project 0)) : False := by
    have hc := (ballot_project_ciphertext names v 0 0).symm.trans
      (he.trans (project_tuple_get zeroFields 0 (by decide)))
    exact zero_not_one ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.2.symm
  simp only [board, List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact exclude 0 he
  · have hm' : earlier = ballot names 1 0 := by simpa using hm
    subst earlier
    exact exclude 1 he

abbrev proofRecipe : Recipe 3 :=
  .spk (.var 0) (.name 40) (.const .zero) (.ternary .penc (.var 0) (.name 40) (.const .zero))

/-- An actual accepted proof has a minimum constructed representative. Its zero
plaintext also excludes the remaining honest aggregate branch in this fixture. -/
theorem accepted_minimum_constructed_proof :
    ∃ s : Recipe 3, MinimalRecipe names.nonceNames (frame names false 0 0).value s ∧
      EqE ((frame names false 0 0).eval s) zeroProof ∧ ∃ a b c d, s = .spk a b c d := by
  have hp : proofRecipe.Public names.nonceNames := by
    change True ∧ 40 ∉ names.nonceNames ∧ True ∧ (True ∧ 40 ∉ names.nonceNames ∧ True)
    decide
  obtain ⟨s, hm, he⟩ := exists_minimal_recipe (σ := (frame names false 0 0).value) proofRecipe hp
  have he' : EqE ((frame names false 0 0).eval s) zeroProof := he.symm
  have hb : ∀ i : Fin 2, ballot names i (choice false 0 0 i) ∈ board := by
    intro i
    fin_cases i <;> simp [board, choice]
  have hs := minimum_accepted_component_proof_form names false 0 0 names.nonceNames board abstention
    abstention_after_both_honest hb 0 s hm
    (he'.trans (project_tuple_get zeroFields 1 (by decide)).symm)
  rcases hs with hc | ⟨i, hr⟩
  · exact ⟨s, hm, he', hc⟩
  · subst s
    have hv : EqE ((frame names false 0 0).eval ((Term.var i.succ).project 2))
        (aggregateProof names i (choice false 0 0 i)) := by
      simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle] using
        ballot_project_aggregate names i (choice false 0 0 i)
    have hbit := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp (he'.symm.trans hv)).2.2.1
    fin_cases i <;> exact False.elim (zero_not_one hbit)

end ExplainableCrypto.Helios.Symbolic.BallotValueSPOT
