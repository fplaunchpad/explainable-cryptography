import ExplainableCrypto.Helios.Symbolic.SourceComputedVoterElection

namespace ExplainableCrypto.Helios.Symbolic.SourceVoterComputationSPOT
open Historical General Source

abbrev names : Names 1 := ⟨40,41,fun i j => 42 + 2*i.val + j.val⟩
abbrev votes : Fin 2 → Ground := fun j => if j=1 then .const .one else .const .zero
abbrev c₀ : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 42) (.const .zero)
abbrev c₁ : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 43) (.const .one)
abbrev p₀ : Ground := .spk (.unary .pk (.name 40)) (.name 42) (.const .zero) c₀
abbrev p₁ : Ground := .spk (.unary .pk (.name 40)) (.name 43) (.const .one) c₁
abbrev expected : Ground := Term.tuple [c₀,c₁,p₀,p₁,
  .spk (.unary .pk (.name 40)) (.binary .compose (.name 42) (.name 43))
    (.binary .add (.const .zero) (.const .one)) (.binary .mul c₀ c₁)]

theorem fixture_names_fresh : names.Fresh := by
  unfold Names.Fresh Function.Injective
  decide

/-- The independently written result retains both ciphertexts, both full
component proofs, and the raw aggregate expression in the expected order. -/
theorem two_candidate_result_exact : (voterProgram names 0 votes).value = expected :=
  voterProgram_value names 0 votes

theorem two_candidate_eight_lets : (voterProgram names 0 votes).bindings = 8 :=
  voterProgram_bindings names 0 votes

theorem explicit_source_outputs_complete_ballot :
    Extended.Structural ((voterProgram names 0 votes).compile 2) (.plain (.output 2 expected .nil)) :=
  voterProgram_normalizes names 0 votes 2

theorem candidate_nonce_swap_rejected :
    ¬ EqE ((voterProgram names 0 votes).value.project 0) c₁ := by
  intro h
  have hc := (General.ballot_project_ciphertext names 0 votes (0 : Fin 2)).symm.trans
    (by simpa only [voterProgram_value,Fin.val_zero] using h)
  have hn := ((EqE.penc_iff _ _ _ _ _ _).mp hc).2.1
  exact (by decide : (42 : Nat) ≠ 43) ((EqE.name_iff 42 43).mp hn)

/-- The aggregate's fourth field is the product of the saved ciphertexts. -/
theorem aggregate_keeps_full_fourth_field :
    EqE ((voterProgram names 0 votes).value.project 4)
      (.spk (.unary .pk (.name 40)) (.binary .compose (.name 42) (.name 43))
        (.binary .add (.const .zero) (.const .one)) (.binary .mul c₀ c₁)) := by
  rw [voterProgram_value]
  exact General.ballot_project_aggregate names 0 votes

abbrev incomplete := voterComponents [0] (voterInitial names 0 votes)

theorem skipped_candidate_reduces_let_count : incomplete.bindings = 6 :=
  voterComponents_bindings [0] (voterInitial names 0 votes)

/-- Skipping the second candidate leaves its ciphertext register at bottom. -/
theorem skipped_candidate_leaves_bottom : EqE (incomplete.value.project 1) (.const .bottom) := by
  have h := voterComponents_eval [0] (voterInitial names 0 votes) Term.var
  rw [TermProgram.eval_var] at h
  rw [h]
  exact (EqE.unary .fst (EqE.equation (.snd _ _))).trans (EqE.equation (.fst _ _))

theorem skipped_candidate_cannot_have_complete_result : incomplete.value ≠ expected := by
  intro h
  have he : EqE (expected.project 1) c₁ := by
    exact General.ballot_project_ciphertext names 0 votes (1 : Fin 2)
  have hb := skipped_candidate_leaves_bottom
  rw [h] at hb
  have hc : EqE c₁ (.const .bottom) := he.symm.trans hb
  have hd := hc.denote (fun _ => 0) Empty.elim
  simp [Term.denote,Term.interpretTernary] at hd

/-- Old variable 8 is shifted past both local definitions; it is not captured
by either fresh None. -/
abbrev openProgram : TermProgram Nat := .letTerm (.var 7)
  (.letTerm (.binary .pair (.var none) (.var (some 8))) (.result (.var none)))

theorem open_variables_survive_both_lets : openProgram.value = .binary .pair (.var 7) (.var 8) := rfl

theorem open_computation_has_no_exported_locals : ∀ v, ¬ (openProgram.compile 2).Exports v :=
  openProgram.compile_no_exports 2

abbrev chooseLeft : CandidateSubstitution 1 Empty := (BitCandidate.selected (0 : Fin 2)).substitution
abbrev chooseRight : CandidateSubstitution 1 Empty := (BitCandidate.selected (1 : Fin 2)).substitution
abbrev ch := Channels.canonical

theorem actual_election_with_computations_is_wellFormed (swap : Bool) :
    (computedVoterElection names swap chooseLeft chooseRight 0 ch).WellFormed :=
  computedVoterElection_wellFormed names swap chooseLeft chooseRight 0 ch

theorem actual_election_initial_static_clause :
    Named.StaticEq (computedVoterElection names false chooseLeft chooseRight 0 ch)
      (computedVoterElection names true chooseLeft chooseRight 0 ch) :=
  computedVoterElection_staticEq names fixture_names_fresh chooseLeft chooseRight 0 ch

theorem actual_election_first_private_communication (swap : Bool) :
    Named.Reduction (computedVoterElection names swap chooseLeft chooseRight 0 ch)
      (Named.restrictedState ch.privateChannels (sourceState names swap chooseLeft chooseRight 0 ch .firstReceived)) := by
  apply (computedVoterElection_reduction_iff names swap chooseLeft chooseRight 0 ch _).mpr
  apply Named.restricted_tau_derivable
  exact ScopedStep.tau _ (residual_receiveFirst names swap chooseLeft chooseRight 0 ch)

abbrev singleNames : Names 0 := ⟨40,41,fun i _ => 60+i.val⟩
abbrev noisyVote : Ground := .unary .fst (.binary .pair (.const .one) (.name 99))
abbrev noisyCipher : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 61) noisyVote
abbrev noisyProof : Ground := .spk (.unary .pk (.name 40)) (.name 61) noisyVote noisyCipher

/-- One candidate still has two component lets and all four aggregate lets. -/
theorem one_candidate_six_lets : (voterProgram singleNames 1 (fun _ => noisyVote)).bindings = 6 :=
  voterProgram_bindings singleNames 1 (fun _ => noisyVote)

/-- Arbitrary full ground representatives survive as syntax; the compiler does
not simplify the vote or omit the proof's complete ciphertext field. -/
theorem nonliteral_ground_vote_retained :
    (voterProgram singleNames 1 (fun _ => noisyVote)).value = Term.tuple [noisyCipher,noisyProof,noisyProof] :=
  voterProgram_value singleNames 1 (fun _ => noisyVote)

end ExplainableCrypto.Helios.Symbolic.SourceVoterComputationSPOT
