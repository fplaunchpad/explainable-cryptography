import ExplainableCrypto.Helios.Symbolic.SourceCanonicalOpening
import ExplainableCrypto.Helios.Symbolic.SourceGuardRetractionSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceOpeningSPOT
open Historical General Source

abbrev payload : Ground := .spk (.name 40) (.name 41) (.const .one) (.name 99)
abbrev code : Agent Empty := .output 8 payload (.input 9 (.output 10 (.var none) .nil))
abbrev privateCode : Named Empty := .newName (.base 40) (.newName (.channel 8) (.embed (.plain code)))
abbrev openedCode : Agent Empty :=
  .output 108 (.spk (.name 100) (.name 41) (.const .one) (.name 99))
    (.input 9 (.output 10 (.var none) .nil))

theorem full_private_opening :
    Named.Opens privateCode NameAssignment.literal [.base 100,.channel 108] (.plain openedCode) :=
  .newName (.base 40) 100 (.newName (.channel 8) 108 (.embed _ _) (by decide)) (by decide)

theorem allocation_is_distinct : ([SourceName.base 100,.channel 108]).Nodup :=
  full_private_opening.nodup

theorem chosen_opening_is_actual_source_structure :
    Named.Structural privateCode
      (Named.restrictNames [.base 100,.channel 108] (.embed (.plain openedCode))) :=
  full_private_opening.structural_literal (by decide)

theorem full_fourth_field_and_waiting_input_survive :
    openedCode = .output 108 (.spk (.name 100) (.name 41) (.const .one) (.name 99))
      (.input 9 (.output 10 (.var none) .nil)) := rfl

theorem opened_body_reconstructs_original_interpretation :
    privateCode.Interprets NameAssignment.literal Empty.elim openedCode :=
  full_private_opening.interprets Empty.elim (.refl _)

theorem duplicate_same_sort_allocations_impossible (a : Named Empty) (b : Extended Empty) :
    ¬ Named.Opens a NameAssignment.literal [.base 100,.base 100] b := by
  intro h
  have hn := h.nodup
  simp at hn

theorem different_sorts_may_share_a_numeral :
    Named.Opens privateCode NameAssignment.literal [.base 100,.channel 100]
      (.plain (.output 100 (.spk (.name 100) (.name 41) (.const .one) (.name 99))
        (.input 9 (.output 10 (.var none) .nil)))) :=
  .newName (.base 40) 100 (.newName (.channel 8) 100 (.embed _ _) (by decide)) (by decide)

abbrev parallelLocals : Named (Fin 2) :=
  .par (.newName (.base 40) (.embed (.active 0 (.name 40))))
    (.newName (.base 40) (.embed (.active 1 (.name 40))))

theorem parallel_same_spelling_keeps_distinct_values :
    Named.Opens parallelLocals NameAssignment.literal [.base 100,.base 101]
      (.par (.active 0 (.name 100)) (.active 1 (.name 101))) :=
  .par (.newName (.base 40) 100 (.embed _ _) (by simp))
    (.newName (.base 40) 101 (.embed _ _) (by simp)) (by decide)

theorem parallel_opening_uses_actual_extrusion :
    Named.Structural parallelLocals
      (Named.restrictNames [.base 100,.base 101]
        (.embed (.par (.active 0 (.name 100)) (.active 1 (.name 101))))) :=
  parallel_same_spelling_keeps_distinct_values.structural_literal (by decide)

theorem shadowed_binder_keeps_inner_value :
    Named.Opens
      (.newName (.base 40) (.newName (.base 40) (.embed (.plain (.output 8 (.name 40) .nil : Agent Empty)))))
      NameAssignment.literal [.base 100,.base 101] (.plain (.output 8 (.name 101) .nil)) :=
  .newName (.base 40) 100 (.newName (.base 40) 101 (.embed _ _) (by simp)) (by decide)

abbrev localProcess : Named Empty := .newVar (.newName (.base 40)
  (.embed (.par (.active none (.name 40)) (.plain (.output 8 (.var none) .nil)))))
abbrev openedLocal : Extended Empty := .newVar
  (.par (.active none (.name 100)) (.plain (.output 8 (.var none) .nil)))

theorem variable_binder_and_constraint_are_retained :
    Named.Opens localProcess NameAssignment.literal [.base 100] openedLocal :=
  .newVar (.newName (.base 40) 100 (.embed _ _) (by simp))

theorem local_value_interpretation_reconstructs :
    localProcess.Interprets NameAssignment.literal Empty.elim (.output 8 (.name 100) .nil) := by
  apply variable_binder_and_constraint_are_retained.interprets Empty.elim
  exact ⟨.name 100,.nil,.output 8 (.name 100) .nil,⟨.refl _,.refl _⟩,.refl _,.of_parEq (.zero_left _)⟩

theorem arbitrary_finite_avoidance_has_actual_opening (avoid : Finset SourceName) :
    ∃ ns b, Named.Opens privateCode NameAssignment.literal ns b ∧ ns.Nodup ∧
      (∀ n ∈ ns, n ∉ avoid ∪ privateCode.allNames) ∧
      Named.Structural privateCode (Named.restrictNames ns (.embed b)) :=
  Named.exists_fresh_opening_structural privateCode avoid

abbrev distinct : Formula Empty := .unequal (.name 40) (.name 41)
abbrev guarded : Named Empty := .newName (.base 40)
  (.embed (.plain (.branch distinct (.output 8 (.name 40) .nil) .nil)))

theorem allocation_alone_does_not_prevent_free_capture :
    Named.Opens guarded NameAssignment.literal [.base 41]
      (.plain (.branch (.unequal (.name 41) (.name 41)) (.output 8 (.name 41) .nil) .nil)) :=
  .newName (.base 40) 41 (.embed _ _) (by simp)

theorem colliding_opening_fails_structural_freshness :
    ¬ (∀ n ∈ [SourceName.base 41], n ∉ guarded.allNames) := by decide

theorem captured_guard_changes_truth :
    distinct.Holds Empty.elim ∧
      ¬ (Formula.unequal (.name 41) (.name 41) : Formula Empty).Holds Empty.elim := by
  constructor
  · intro h
    have he := (EqE.name_iff 40 41).mp h
    cases he
  · intro h
    exact h (.refl _)

abbrev state : ScopedState {40} 1 :=
  ⟨⟨fun _ => payload⟩,.branch distinct code .nil⟩

theorem canonical_witnesses_are_constructed (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (b : Extended (Fin 1)) (e k : Nat ≃ Nat),
      Named.Opens (Named.restrictedState {8} state) NameAssignment.literal ns b ∧ ns.Nodup ∧
      (∀ n ∈ ns, n ∉ avoid) ∧
      Named.Structural (Named.restrictedState {8} state) (Named.restrictNames ns (.embed b)) ∧
      b = Extended.frameProcess (state.frame.mapNames e) (state.body.mapNames e k) ∧
      b.Realizes (state.frame.mapNames e).value (state.body.mapNames e k) ∧
      state.body.ReadyGuardsRetract e e.symm :=
  Named.exists_fresh_canonical_opening state avoid

theorem actual_election_check_has_fresh_permuted_body (swap : Bool) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (b : Extended (Fin 3)) (e k : Nat ≃ Nat),
      Named.Structural
        (Named.restrictedState Channels.canonical.privateChannels
          (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.check [] (.var 1))))
        (Named.restrictNames ns (.embed b)) ∧
      (∀ n ∈ ns, n ∉ avoid) ∧
      b.Realizes
        ((sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right (.check [] (.var 1))).mapNames e).value
        ((residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.check [] (.var 1))).mapNames e k) := by
  obtain ⟨ns,b,e,k,_,_,hf,hs,_,hr,_⟩ := Named.exists_fresh_canonical_opening
    (hidden := Channels.canonical.privateChannels)
    (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.check [] (.var 1))) avoid
  exact ⟨ns,b,e,k,hs,hf,hr⟩

end ExplainableCrypto.Helios.Symbolic.SourceOpeningSPOT
