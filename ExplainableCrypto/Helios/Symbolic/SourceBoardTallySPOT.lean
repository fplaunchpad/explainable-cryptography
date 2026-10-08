import ExplainableCrypto.Helios.Symbolic.SourceBoardTallyBridge
import ExplainableCrypto.Helios.Symbolic.SourceVoterComputationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceBoardTallySPOT
open Historical General Source

abbrev ch := Channels.canonical
abbrev first : Ground := Term.tuple [.name 11,.name 12]
abbrev second : Ground := Term.tuple [.name 21,.name 22]
abbrev third : Ground := Term.tuple [.name 31,.name 32]
abbrev product₀ : Ground := .binary .mul (.binary .mul (.name 11) (.name 21)) (.name 31)
abbrev product₁ : Ground := .binary .mul (.binary .mul (.name 12) (.name 22)) (.name 32)
abbrev raw₀ : Ground := .binary .mul (.binary .mul (first.project 0) (second.project 0)) (third.project 0)
abbrev raw₁ : Ground := .binary .mul (.binary .mul (first.project 1) (second.project 1)) (third.project 1)
abbrev program := boardTallyProgram (n := 1) ch first second [third]

private def sent {V : Type} : Agent V → Term V
  | .output _ m _ => m
  | _ => .const .bottom

private theorem raw_first : EqE raw₀ product₀ :=
  .binary .mul (.binary .mul (.equation (.fst _ _)) (.equation (.fst _ _))) (.equation (.fst _ _))

private theorem raw_second : EqE raw₁ product₁ := by
  have project (a b : Ground) : EqE ((Term.tuple [a,b]).project 1) b :=
    (EqE.unary .fst (.equation (.snd _ _))).trans (.equation (.fst _ _))
  exact .binary .mul (.binary .mul (project _ _) (project _ _)) (project _ _)

theorem two_candidates_bind_twice : program.bindings = 2 := boardTallyProgram_bindings ch first second [third]

/-- Independent literal continuation: private tally tuple, fresh trustee
input, public partial tuple, then decryptions using each saved raw product. -/
theorem complete_ordered_continuation : program.value =
    .output 1 (Term.tuple [raw₀,raw₁]) (.input 1
      (.output 0 (.var none) (.output 0 (Term.tuple
        [.binary .dec ((Term.var none).project 0) (shiftTerm raw₀),
         .binary .dec ((Term.var none).project 1) (shiftTerm raw₁)]) .nil))) :=
  boardTallyProgram_value ch first second [third]

theorem first_product_uses_three_ballots : EqE ((sent program.value).project 0) product₀ := by
  rw [boardTallyProgram_value]
  exact (candidateTuple_project (boardTally first second [third]) (0 : Fin 2)).trans raw_first

theorem second_product_uses_three_ballots : EqE ((sent program.value).project 1) product₁ := by
  rw [boardTallyProgram_value]
  exact (candidateTuple_project (boardTally first second [third]) (1 : Fin 2)).trans raw_second

/-- The sound separating algebra only refutes equality; it is not attacker
semantics and supplies no positive secrecy claim. -/
theorem copying_first_candidate_is_rejected : ¬ EqE ((sent program.value).project 1) product₀ := by
  intro h
  have he := (second_product_uses_three_ballots.symm.trans h).denote id Empty.elim
  change 66 = 63 at he
  omega

abbrev incomplete := boardTallyComponents ch [0] (boardTallyInitial (n := 1) first second [third])

theorem omitted_candidate_has_one_let : incomplete.bindings = 1 :=
  boardTallyComponents_bindings ch [0] (boardTallyInitial first second [third])

theorem omitted_candidate_stays_bottom : EqE ((sent incomplete.value).project 1) (.const .bottom) := by
  have h := boardTallyComponents_eval ch [0] (boardTallyInitial (n := 1) first second [third]) Term.var
  rw [AgentProgram.eval_var] at h
  rw [h]
  exact (EqE.unary .fst (.equation (.snd _ _))).trans (.equation (.fst _ _))

theorem omitted_candidate_cannot_send_complete_message : sent incomplete.value ≠ sent program.value := by
  intro h
  have hb := omitted_candidate_stays_bottom
  rw [h] at hb
  have he := (second_product_uses_three_ballots.symm.trans hb).denote id Empty.elim
  change 66 = 2 at he
  omega

theorem no_tally_local_is_exported (v : Nat) :
    ¬ (boardTallyProgram (n := 1) ch (.var 7) (.var 8) [.var 9]).compile.Exports v :=
  (boardTallyProgram (n := 1) ch (.var 7) (.var 8) [.var 9]).compile_no_exports v

abbrev openProgram : AgentProgram Nat := .letTerm (.var 7)
  (.letTerm (.var (some 8)) (.result (.input 1 (.output 0
    (.binary .pair (.var none) (.binary .pair (.var (some (some none))) (.var (some none)))) .nil))))

theorem trustee_input_does_not_capture_saved_tallies : openProgram.value =
    .input 1 (.output 0 (.binary .pair (.var none)
      (.binary .pair (.var (some 7)) (.var (some 8)))) .nil) := rfl

theorem captured_tally_mutant_differs : openProgram.value ≠
    .input 1 (.output 0 (.binary .pair (.var none)
      (.binary .pair (.var none) (.var (some 8)))) .nil) := by
  intro h
  simp only [trustee_input_does_not_capture_saved_tallies] at h
  cases h

theorem open_locals_normalize_with_future_input : Extended.Structural openProgram.compile
    (.plain (.input 1 (.output 0 (.binary .pair (.var none)
      (.binary .pair (.var (some 7)) (.var (some 8)))) .nil))) :=
  openProgram.compile_normalizes

abbrev rewriteTemplate : Agent (Fin 2) := .input 9 (.output 0
  (.binary .pair (.var none) (.binary .pair (.var (some 0)) (.var (some 1)))) .nil)
abbrev before : Fin 2 → Ground := ![.unary .fst (.binary .pair (.name 40) (.name 99)),.name 41]
abbrev after : Fin 2 → Ground := ![.name 40,.name 41]

theorem full_E_rewrite_beneath_future_input :
    Extended.Structural (.plain (rewriteTemplate.subst before)) (.plain (rewriteTemplate.subst after)) := by
  apply rewriteTemplate.finite_subst_structural
  intro i
  fin_cases i
  · exact .equation (.fst _ _)
  · exact .refl _

theorem distinct_saved_values_cannot_be_identified : ¬ EqE (after 0) (after 1) := by
  intro h
  exact (by decide : (40 : Nat) ≠ 41) ((EqE.name_iff 40 41).mp h)

abbrev names := SourceVoterComputationSPOT.names
abbrev left := SourceVoterComputationSPOT.chooseLeft
abbrev right := SourceVoterComputationSPOT.chooseRight

theorem reached_explicit_tally_state_is_wellFormed (swap : Bool) :
    (computedBoardTallyState names swap left right [] ch).WellFormed :=
  computedBoardTallyState_wellFormed names swap left right [] ch

theorem actual_private_send_is_enabled (swap : Bool) :
    Named.Reduction (computedBoardTallyState names swap left right [] ch)
      (Named.restrictedState ch.privateChannels (sourceState names swap left right 0 ch (.trusteeReply []))) :=
  computedBoardTallyState_sends names swap left right [] 0 ch

theorem reached_explicit_tally_static_clause :
    Named.StaticEq (computedBoardTallyState names false left right [] ch)
      (computedBoardTallyState names true left right [] ch) := by
  apply computedBoardTallyState_staticEq SourceVoterComputationSPOT.fixture_names_fresh (extra := 0)
  exact (((Relation.ReflTransGen.refl.tail ⟨.tau,Process.Step.receiveFirst⟩).tail
    ⟨.output 1,Process.Step.publishFirst⟩).tail ⟨.tau,Process.Step.receiveSecond⟩).tail
      ⟨.output 2,Process.Step.publishSecond⟩

/-- The minimum supported election has one candidate and two ballots; its
product is seeded by both ballots, with no artificial identity term. -/
abbrev single := boardTallyProgram (n := 0) ch
  (Term.tuple [.name 7] : Ground) (Term.tuple [.name 8]) []

theorem one_candidate_one_let : single.bindings = 1 :=
  boardTallyProgram_bindings ch _ _ _

theorem two_ballots_nonempty_product :
    EqE ((sent single.value).project 0) (.binary .mul (.name 7) (.name 8)) := by
  rw [boardTallyProgram_value]
  apply (candidateTuple_project (boardTally _ _ []) (0 : Fin 1)).trans
  exact .binary .mul (.equation (.fst _ _)) (.equation (.fst _ _))

end ExplainableCrypto.Helios.Symbolic.SourceBoardTallySPOT
