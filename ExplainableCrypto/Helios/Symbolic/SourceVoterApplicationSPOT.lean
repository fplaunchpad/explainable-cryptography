import ExplainableCrypto.Helios.Symbolic.SourceAppliedElectionActions
import ExplainableCrypto.Helios.Symbolic.SourceVoterScopeSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceVoterApplicationSPOT
open Historical General Source

abbrev names := SourceVoterComputationSPOT.names
abbrev votes := SourceVoterComputationSPOT.votes
abbrev expected := SourceVoterComputationSPOT.expected
abbrev left := SourceVoterComputationSPOT.chooseLeft
abbrev right := SourceVoterComputationSPOT.chooseRight
abbrev ch := Channels.canonical

theorem key_and_votes_have_distinct_parameters :
    voterParameters names votes none = .unary .pk (.name 40) ∧
    voterParameters names votes (some 0) = .const .zero ∧
    voterParameters names votes (some 1) = .const .one := ⟨rfl,rfl,rfl⟩

theorem confusing_key_with_first_vote_changes_the_term :
    voterParameters names votes none ≠ voterParameters names votes (some 0) := by decide

theorem applied_open_template_keeps_all_eight_lets :
    ((voterTemplate names 0).subst (voterParameters names votes)).erase.bindings = 8 := by
  rw [voterTemplate_apply,scopedVoterProgram_erase]
  exact voterProgram_bindings names 0 votes

theorem applied_open_template_has_complete_ballot :
    ((voterTemplate names 0).subst (voterParameters names votes)).erase.value = expected := by
  rw [voterTemplate_apply,scopedVoterProgram_erase]
  exact voterProgram_value names 0 votes

theorem actual_source_template_instantiates :
    Named.Instantiates (voterParameters names votes) ((voterTemplate names 0).compile 2)
      ((scopedVoterProgram names 0 votes).compile 2) :=
  voterTemplate_instantiates names SourceVoterComputationSPOT.fixture_names_fresh 0 votes
    SourceVoterScopeSPOT.literal_parameters_are_fresh 2

theorem applied_template_reaches_complete_output :
    Named.Structural (((voterTemplate names 0).subst (voterParameters names votes)).compile 2)
      (.newName (.base 42) (.newName (.base 43) (.embed (.plain (.output 2 expected .nil))))) :=
  applied_voter_normalizes names SourceVoterComputationSPOT.fixture_names_fresh 0 votes
    SourceVoterScopeSPOT.literal_parameters_are_fresh 2

abbrev localProgram : ScopedTermProgram Nat := .letTerm (.var 7)
  (.newName 50 (.result (.binary .pair (.var none) (.var (some 8)))))
abbrev supply : Nat → Term (Option Nat) := fun j => if j=7 then .var none else .var (some j)

/-- The free None in the supplied term is shifted through the source's fresh
let binder and restored as free None after that local definition is eliminated. -/
theorem supplied_free_variable_survives_local_binding :
    (localProgram.subst supply).erase.value = .binary .pair (.var none) (.var (some 8)) := rfl

theorem source_provider_does_not_capture_supplied_none :
    (localProgram.subst supply).compile 2 =
      .newVar (.par (.embed (.active none (.var (some none))))
        (.newName (.base 50) (.embed (.plain (.output 2
          (.binary .pair (.var none) (.var (some (some 8)))) .nil))))) := rfl

theorem local_application_has_exact_source_graph :
    Named.Instantiates supply (localProgram.compile 2) ((localProgram.subst supply).compile 2) := by
  apply localProgram.compile_instantiates
  intro n hn v
  by_cases hv : v=7 <;> simp [supply,hv,Term.nameSupport]

abbrev boundUse (m : Nat) : Named (Fin 1) := .newName (.base m) (.embed (.plain (.output 2 (.var 0) .nil)))
abbrev supplyName (m : Nat) : Fin 1 → Ground := fun _ => .name m

theorem capturing_name_application_is_rejected :
    ¬ ∃ b : Named Empty, Named.Instantiates (supplyName 50) (boundUse 50) b := by
  rintro ⟨b,h⟩
  cases h with
  | newName _ hf _ => exact hf 0 (by decide)

theorem fresh_name_application_retains_free_payload :
    Named.Instantiates (supplyName 50) (boundUse 51)
      (.newName (.base 51) (.embed (.plain (.output 2 (.name 50) .nil)))) :=
  .newName (.base 51) (by intro v; simp [Term.nameSupport]) (.embed (.plain _ _))

theorem ground_term_cannot_replace_active_domain :
    ¬ ∃ b : Named Empty, Named.Instantiates (supplyName 50) (.embed (.active (0 : Fin 1) (.var 0))) b := by
  rintro ⟨b,h⟩
  cases h with
  | embed he => cases he with | active _ _ y _ _ => exact y.elim

theorem key_domain_remains_an_exported_variable (swap : Bool) :
    electionCandidateSubst swap left right (.inl 0) = .var 0 :=
  electionCandidateSubst_key_domain swap left right 0

abbrev fullProof : ScopedTermProgram (Fin 1) := .result
  (.spk (.const .zero) (.const .one) (.const .zero) (.var 0))

theorem application_retains_full_fourth_field :
    (fullProof.subst (supplyName 99)).erase.value =
      .spk (.const .zero) (.const .one) (.const .zero) (.name 99) := rfl

abbrev hiddenNameSupply : Fin 1 → Ground := fun _ =>
  .spk (.const .zero) (.const .zero) (.const .zero) (.name 50)

theorem fourth_field_name_capture_is_rejected :
    ¬ ∃ b : Named Empty, Named.Instantiates hiddenNameSupply (boundUse 50) b := by
  rintro ⟨b,h⟩
  cases h with
  | newName _ hf _ => exact hf 0 (by decide)

private theorem parameter_fresh : ElectionParametersFresh names left right := by
  intro m hm ha
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp ha
  fin_cases j <;> exact (Finset.notMem_empty m) hj

/-- The graph covers the actual outer restrictions and key active substitution,
not just a helper result term or an isolated voter. -/
theorem whole_open_election_instantiates (swap : Bool) (extra : Nat) :
    Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate names extra ch)
      (scopedVoterElection names swap left right extra ch) :=
  openElectionTemplate_instantiates names left right parameter_fresh swap extra ch

theorem whole_application_normalizes (swap : Bool) (extra : Nat) :
    Named.Structural (scopedVoterElection names swap left right extra ch)
      (Named.restrictedState ch.privateChannels (sourceState names swap left right extra ch .start)) :=
  instantiatedElection_normalizes names SourceVoterComputationSPOT.fixture_names_fresh left right
    parameter_fresh swap extra ch (whole_open_election_instantiates swap extra)

theorem whole_application_is_wellFormed (swap : Bool) :
    (scopedVoterElection names swap left right 0 ch).WellFormed :=
  instantiatedElection_wellFormed names SourceVoterComputationSPOT.fixture_names_fresh left right
    parameter_fresh swap 0 ch (whole_open_election_instantiates swap 0)

theorem two_applications_have_full_initial_static_witness :
    Named.StaticEq (scopedVoterElection names false left right 0 ch)
      (scopedVoterElection names true left right 0 ch) :=
  instantiatedElection_staticEq names SourceVoterComputationSPOT.fixture_names_fresh left right
    parameter_fresh 0 ch (whole_open_election_instantiates false 0) (whole_open_election_instantiates true 0)

theorem actual_application_performs_private_communication (swap : Bool) :
    Named.Reduction (scopedVoterElection names swap left right 0 ch)
      (Named.restrictedState ch.privateChannels (sourceState names swap left right 0 ch .firstReceived)) :=
  instantiatedElection_receivesFirst names SourceVoterComputationSPOT.fixture_names_fresh left right
    parameter_fresh swap 0 ch (whole_open_election_instantiates swap 0)

abbrev hiddenKeyVote : Ground := .unary .fst (.binary .pair (.const .zero) (.name 40))
def hiddenKeyCandidate : CandidateSubstitution 1 Empty :=
  ⟨fun j => if j=0 then hiddenKeyVote else .const .one,
    right.valid.congr (fun j => by
      fin_cases j
      · exact (EqE.equation (.fst _ _)).symm
      · exact .refl _)⟩

theorem hidden_key_parameter_still_represents_zero : EqE (hiddenKeyCandidate.value 0) (.const .zero) :=
  .equation (.fst _ _)

theorem nonce_freshness_does_not_cover_outer_key_scope :
    NoncesFreshFor names hiddenKeyCandidate.value ∧ ¬ ElectionParametersFresh names hiddenKeyCandidate right := by
  constructor
  · intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide
  · intro h
    exact h 40 (by decide) (by decide)

/-- Arbitrary valid terms, including the hidden-key representative, have a
common fresh allocation supporting actual whole-template instantiation. -/
theorem arbitrary_candidates_admit_whole_application (a b : CandidateSubstitution 1 Empty) :
    ∃ ns : Names 1, ns.Fresh ∧ ElectionParametersFresh ns a b ∧ ∀ extra channels swap,
      Named.Instantiates (electionCandidateSubst swap a b) (openElectionTemplate ns extra channels)
        (scopedVoterElection ns swap a b extra channels) ∧
      Named.Structural (scopedVoterElection ns swap a b extra channels)
        (Named.restrictedState channels.privateChannels (sourceState ns swap a b extra channels .start)) :=
  exists_open_election_application a b

end ExplainableCrypto.Helios.Symbolic.SourceVoterApplicationSPOT
