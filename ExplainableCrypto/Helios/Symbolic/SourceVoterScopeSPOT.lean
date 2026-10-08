import ExplainableCrypto.Helios.Symbolic.SourceScopedElectionActions
import ExplainableCrypto.Helios.Symbolic.SourceVoterComputationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceVoterScopeSPOT
open Historical General Source

abbrev names := SourceVoterComputationSPOT.names
abbrev votes := SourceVoterComputationSPOT.votes
abbrev expected := SourceVoterComputationSPOT.expected
abbrev scopeProgram := scopedVoterProgram names 0 votes

theorem literal_parameters_are_fresh : NoncesFreshFor names votes := by
  intro i j k
  fin_cases k <;> exact Finset.notMem_empty _

private def trace : {V : Type} → ScopedTermProgram V → List (Nat × Nat)
  | _, .result _ => [(0,0)]
  | _, .letTerm _ p => (1,0) :: trace p
  | _, .newName n p => (2,n) :: trace p

/-- The second nonce scope starts after the first ciphertext and proof lets;
four aggregate lets follow the second candidate's two local definitions. -/
theorem literal_interleaved_scope_order : trace scopeProgram =
    [(2,42),(1,0),(1,0),(2,43),(1,0),(1,0),(1,0),(1,0),(1,0),(1,0),(0,0)] := rfl

theorem both_nonce_restrictions_retained : scopeProgram.names.map SourceName.base = [.base 42,.base 43] :=
  scopedVoterProgram_names names 0 votes

theorem all_eight_lets_retained : scopeProgram.erase.bindings = 8 := by
  rw [scopedVoterProgram_erase]
  exact voterProgram_bindings names 0 votes

theorem actual_interleaved_voter_outputs_full_ballot :
    Named.Structural (scopeProgram.compile 2)
      (.newName (.base 42) (.newName (.base 43) (.embed (.plain (.output 2 expected .nil))))) :=
  scopedVoterProgram_normalizes names SourceVoterComputationSPOT.fixture_names_fresh 0 votes literal_parameters_are_fresh 2

abbrev noisyZero : Ground := .unary .fst (.binary .pair (.const .zero) (.name 43))
abbrev noisyVotes : Fin 2 → Ground := fun j => if j=0 then noisyZero else .const .one

theorem discarded_nonce_still_equals_zero : EqE noisyZero (.const .zero) := .equation (.fst _ _)

theorem discarded_nonce_is_not_fresh : ¬ NoncesFreshFor names noisyVotes := by
  intro h
  exact h 0 1 0 (by decide)

/-- A later nonce is present in the first ciphertext provider's full vote
term. The general scope rule correctly refuses that unsafe extrusion. -/
theorem discarded_nonce_blocks_hoisting_criterion :
    ¬ (scopedVoterProgram names 0 noisyVotes).Hoistable := by
  intro h
  exact h.2 43 (by decide) (by decide)

theorem distinct_allocation_does_not_imply_parameter_freshness :
    names.Fresh ∧ ¬ NoncesFreshFor names noisyVotes :=
  ⟨SourceVoterComputationSPOT.fixture_names_fresh,discarded_nonce_is_not_fresh⟩

abbrev allocated := allocateElectionNames 1 100

theorem fresh_allocation_has_disjoint_nonce_slots :
    allocated.secretKey = 100 ∧ allocated.auxiliary = 101 ∧
    allocated.nonce 0 0 = 102 ∧ allocated.nonce 0 1 = 103 ∧
    allocated.nonce 1 0 = 104 ∧ allocated.nonce 1 1 = 105 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem concrete_allocation_is_fresh : allocated.Fresh := allocateElectionNames_fresh 1 100

theorem fresh_allocation_preserves_noisy_parameters : NoncesFreshFor allocated noisyVotes := by
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

theorem noisy_parameters_work_after_fresh_allocation :
    Named.Structural ((scopedVoterProgram allocated 0 noisyVotes).compile 2)
      (Named.restrictNames [.base 102,.base 103]
        (.embed (.plain (.output 2 (General.ballot allocated 0 noisyVotes) .nil)))) :=
  scopedVoterProgram_normalizes allocated concrete_allocation_is_fresh 0 noisyVotes
    fresh_allocation_preserves_noisy_parameters 2

theorem arbitrary_full_parameters_admit_fresh_names (left right : Fin 2 → Ground) :
    ∃ ns : Names 1, ns.Fresh ∧ NoncesFreshFor ns left ∧ NoncesFreshFor ns right ∧
      (∀ m ∈ ns.restricted, m ∉ candidateParameterNames left right) :=
  exists_parameter_fresh_election left right

abbrev ch := Channels.canonical
abbrev administration : Named Empty := .embed (.plain
  (.par (boardStart 1 0 ch (publicKey names)) (trusteeAgent (n := 1) ch (.name 40))))

private theorem administration_fresh :
    ∀ u ∈ voterNonceList names 0 ++ voterNonceList names 1, u ∉ administration.freeNames := by
  intro u hu
  change u ∈ [.base 42,.base 43,.base 44,.base 45] at hu
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> decide

/-- Both scope-bearing voters are beside the actual board and trustee; all
four nonce scopes move outside that context without changing its code. -/
theorem actual_two_voters_hoist_beside_administration :
    Named.Structural (scopedVotersWith names votes votes 2 3 administration)
      (Named.restrictNames [.base 42,.base 43,.base 44,.base 45]
        (.par (voterOutput names 0 votes 2) (.par (voterOutput names 1 votes 3) administration))) :=
  scopedVotersWith_normalizes names SourceVoterComputationSPOT.fixture_names_fresh votes votes
    literal_parameters_are_fresh literal_parameters_are_fresh 2 3 administration administration_fresh

abbrev capturingContext : Named Empty := .embed (.plain (.output 0 (.name 43) .nil))

theorem context_using_nonce_fails_extrusion_premise :
    ¬ (∀ u ∈ voterNonceList names 0 ++ voterNonceList names 1, u ∉ capturingContext.freeNames) := by
  intro h
  exact h (.base 43) (by decide) (by decide)

/-- A proof's fourth field contributes to the provider freshness check even
when the other three fields contain no names. -/
abbrev fourthField : ScopedTermProgram Empty :=
  .letTerm (.spk (.const .zero) (.const .zero) (.const .zero) (.name 43))
    (.newName 43 (.result (.var none)))

theorem full_fourth_field_blocks_hoisting : ¬ fourthField.Hoistable := by
  intro h
  exact h.2 43 (by decide) (by decide)

abbrev safeLocal : ScopedTermProgram Nat := .letTerm (.var 7)
  (.newName 43 (.result (.binary .pair (.var none) (.var (some 8)))))

theorem local_variables_survive_name_hoisting :
    Named.Structural (safeLocal.compile 2)
      (.newName (.base 43) (.embed (.plain (.output 2 (.binary .pair (.var 7) (.var 8)) .nil)))) :=
  safeLocal.compile_normalizes 2 ⟨trivial,by simp [ScopedTermProgram.names,Term.nameSupport]⟩

abbrev left := SourceVoterComputationSPOT.chooseLeft
abbrev right := SourceVoterComputationSPOT.chooseRight

private theorem left_fresh : NoncesFreshFor names left.value := by
  intro i j k
  fin_cases k <;> exact Finset.notMem_empty _

private theorem right_fresh : NoncesFreshFor names right.value := by
  intro i j k
  fin_cases k <;> exact Finset.notMem_empty _

theorem complete_initial_scope_correspondence (swap : Bool) (extra : Nat) :
    Named.Structural (scopedVoterElection names swap left right extra ch)
      (Named.restrictedState ch.privateChannels (sourceState names swap left right extra ch .start)) :=
  scopedVoterElection_normalizes names SourceVoterComputationSPOT.fixture_names_fresh swap
    left right left_fresh right_fresh extra ch

theorem actual_scope_election_initial_static_clause :
    Named.StaticEq (scopedVoterElection names false left right 0 ch)
      (scopedVoterElection names true left right 0 ch) :=
  scopedVoterElection_staticEq names SourceVoterComputationSPOT.fixture_names_fresh
    left right left_fresh right_fresh 0 ch

theorem actual_scope_election_is_wellFormed (swap : Bool) :
    (scopedVoterElection names swap left right 0 ch).WellFormed :=
  scopedVoterElection_wellFormed names SourceVoterComputationSPOT.fixture_names_fresh swap
    left right left_fresh right_fresh 0 ch

theorem actual_scope_election_first_private_communication (swap : Bool) :
    Named.Reduction (scopedVoterElection names swap left right 0 ch)
      (Named.restrictedState ch.privateChannels (sourceState names swap left right 0 ch .firstReceived)) :=
  scopedVoterElection_receivesFirst names SourceVoterComputationSPOT.fixture_names_fresh swap
    left right left_fresh right_fresh 0 ch

theorem arbitrary_candidates_share_one_fresh_initial_allocation
    (a b : CandidateSubstitution 1 Empty) :
    ∃ ns : Names 1, ns.Fresh ∧ ∀ extra channels,
      (∀ swap, Named.Structural (scopedVoterElection ns swap a b extra channels)
        (Named.restrictedState channels.privateChannels (sourceState ns swap a b extra channels .start))) ∧
      Named.StaticEq (scopedVoterElection ns false a b extra channels)
        (scopedVoterElection ns true a b extra channels) :=
  exists_scoped_election_correspondence a b

/-- Prefix canonicalization keeps the exact base/channel set while removing
only duplicate occurrences. -/
theorem duplicate_prefix_is_canonicalized (p : Named Empty) :
    Named.Structural (Named.restrictNames [.base 40,.channel 9,.base 40] p)
      (Named.restrictNames [.channel 9,.base 40] p) :=
  Named.Structural.restrictNames_of_toFinset_eq _ _ (by decide) p

/-- Used channel restriction cannot be discarded by the prefix-set theorem. -/
theorem used_channel_is_not_removed :
    ¬ Named.Structural (.newName (.channel 9) (.embed (.plain (.input 9 .nil : Agent Empty))))
      (.embed (.plain (.input 9 .nil : Agent Empty))) := by
  intro h
  have he := h.channels
  simp [Named.channels,Extended.channels,Agent.channels] at he

end ExplainableCrypto.Helios.Symbolic.SourceVoterScopeSPOT
