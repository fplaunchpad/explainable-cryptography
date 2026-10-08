import ExplainableCrypto.Helios.Symbolic.SourceFreshElectionInternal
import ExplainableCrypto.Helios.Symbolic.SourceOpeningSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceOpeningComparisonSPOT
open Historical General Source

abbrev zero : Named Empty := .embed (.plain .nil)

theorem unused_restriction_can_be_removed :
    Named.OpeningEquivalent (.newName (.base 40) zero) zero :=
  (Named.Structural.nameZero _).openingEquivalent

theorem unused_restriction_requires_a_different_list :
    ¬ Named.Opens zero NameAssignment.literal [.base 100] (.plain .nil) := by
  intro h; cases h

theorem inverse_unused_restriction_preserves_any_avoidance (avoid : Finset SourceName) :
    ∃ ns b, Named.Opens (.newName (.base 40) zero) NameAssignment.literal ns b ∧
      (∀ n ∈ ns, n ∉ avoid) ∧ (Extended.plain (.nil : Agent Empty)).SameRealizations b := by
  obtain ⟨ns, b, hb, hf, he⟩ :=
    unused_restriction_can_be_removed.2 _ [] _ avoid (.embed _ _) (by simp)
  exact ⟨ns, b, hb, hf, he.sameRealizations⟩

abbrev left : Named (Fin 1) := .embed (.active 0 (.name 41))
abbrev right : Named (Fin 1) := .embed (.plain (.output 8 (.name 40) .nil))

theorem source_extrusion_is_available :
    Named.Structural (.par left (.newName (.base 40) right))
      (.newName (.base 40) (.par left right)) := .namePar _ _ _ (by decide)

theorem extrusion_preserves_all_full_realizations :
    Named.OpeningEquivalent (.par left (.newName (.base 40) right))
      (.newName (.base 40) (.par left right)) := source_extrusion_is_available.openingEquivalent

theorem capture_breaks_extrusion_side_condition : SourceName.base 41 ∈ left.freeNames := by decide

abbrev alphaBody : Named (Fin 1) := .embed (.par (.active 0 (.name 40))
  (.plain (.output 8 (.spk (.name 40) (.name 41) (.const .one) (.name 99)) .nil)))

theorem base_alpha_preserves_chosen_opening :
    Named.Opens (.newName (.base 50) (alphaBody.mapNames (Equiv.swap 40 50) id))
      NameAssignment.literal [.base 100]
      (.par (.active 0 (.name 100))
        (.plain (.output 8 (.spk (.name 100) (.name 41) (.const .one) (.name 99)) .nil))) :=
  (Named.opens_alpha_iff alphaBody (.base 40) (.base 50) (Equiv.swap 40 50)
    (Equiv.refl Nat) (SourceName.map_base_swap_eq _ _) (by decide) (fun _ => rfl) _ _ _).mp
    (.newName (.base 40) 100 (.embed _ _) (by simp))

theorem channel_alpha_preserves_full_program :
    Named.OpeningEquivalent (.newName (.channel 8) alphaBody)
      (.newName (.channel 18) (alphaBody.mapNames id (Equiv.swap 8 18))) :=
  (Named.Structural.alphaChannel alphaBody 8 18 (by decide)).openingEquivalent

theorem existing_fourth_field_cannot_be_alpha_target : SourceName.base 99 ∈ alphaBody.allNames := by decide

theorem unequal_active_values_are_not_same_realizations :
    ¬ (Extended.active (0 : Fin 1) (.name 40)).SameRealizations (.active 0 (.name 41)) := by
  intro h
  have hb := (h (fun _ => .name 40) .nil).mp ⟨.refl _,.refl _⟩
  have he := (EqE.name_iff 40 41).mp hb.1
  cases he

theorem dead_field_rewrite_preserves_active_constraints :
    (Extended.active (0 : Fin 1) (.name 40)).SameRealizations
      (.active 0 (.unary .fst (.binary .pair (.name 40) (.name 99)))) :=
  (Extended.Structural.rewrite _ (EqE.equation (.fst (.name 40) (.name 99))).symm).sameRealizations

abbrev variableBody : Named (Option (Option Empty)) := .embed
  (.par (.active none (.name 40)) (.plain (.output 8 (.var (some none)) .nil)))

theorem variable_swap_compares_full_openings :
    Named.OpeningEquivalent (.newVar (.newVar variableBody))
      (.newVar (.newVar (variableBody.rename Extended.swapBinders))) :=
  (Named.Structural.varComm variableBody).openingEquivalent

theorem same_spelling_nested_names_are_covered :
    Named.OpeningEquivalent (.newName (.base 40) (.newName (.base 40) alphaBody))
      (.newName (.base 40) (.newName (.base 40) alphaBody)) :=
  (Named.Structural.nameComm _ _ alphaBody).openingEquivalent

theorem distinct_name_sorts_commute :
    Named.OpeningEquivalent (.newName (.base 40) (.newName (.channel 40) alphaBody))
      (.newName (.channel 40) (.newName (.base 40) alphaBody)) :=
  (Named.Structural.nameComm _ _ alphaBody).openingEquivalent

abbrev guard : Formula Empty := .unequal (.name 40) (.name 41)
abbrev good : Agent Empty := .output 8 (.name 40) .nil
abbrev bad : Agent Empty := .output 9 (.name 41) .nil
abbrev rawBranch : Extended Empty := .plain (.branch guard good bad)
abbrev rawTarget : Extended Empty := .plain good

theorem distinct_guard_takes_then : Extended.Reduction rawBranch rawTarget :=
  .thenBranch guard good bad (by intro h; have he := (EqE.name_iff 40 41).mp h; cases he)

theorem fresh_conditional_opening_keeps_actual_step :
    ∃ q, Agent.Tau (.branch (.unequal (.name 100) (.name 41)) (.output 8 (.name 100) .nil) bad) q ∧
      (Named.restrictNames [.base 40] (.embed rawTarget)).Interprets NameAssignment.literal Empty.elim q := by
  apply Named.Opens.prefix_reduction_realizes [.base 40] distinct_guard_takes_then
    NameAssignment.literal (.newName (.base 40) 100 (.embed rawBranch _) (by simp))
  · intro a b ha hb he; cases a <;> cases b <;> exact he
  · decide
  · exact Agent.EvalEq.refl _

theorem captured_allocation_is_excluded_by_endpoint_support :
    SourceName.base 41 ∈ rawBranch.nameSupport ∪ rawTarget.nameSupport := by decide

abbrev state : ScopedState {40} 1 := ⟨⟨fun _ => .name 40⟩,.branch guard good bad⟩
abbrev target : ScopedState {40} 1 := ⟨state.frame,good⟩

theorem actual_canonical_conditional :
    Named.Reduction (Named.restrictedState ∅ state) (Named.restrictedState ∅ target) :=
  Named.restricted_tau_derivable _ _ (.tau state.frame (Agent.Tau.of_core (.thenBranch guard good bad
    (by intro h; have he := (EqE.name_iff 40 41).mp h; cases he))))

theorem arbitrary_source_representative_has_fresh_actual_tau
    (a b : Named (Fin 1)) (ha : Named.Structural (Named.restrictedState ∅ state) a)
    (h : Named.Reduction a b) (avoid : Finset SourceName) :
    ∃ (ns : List SourceName) (c : Extended (Fin 1)) (e k : Nat ≃ Nat) (q : Agent Empty),
      Named.Opens (Named.restrictedState ∅ state) NameAssignment.literal ns c ∧ ns.Nodup ∧
      (∀ n ∈ ns, n ∉ avoid) ∧
      Named.Structural (Named.restrictedState ∅ state) (Named.restrictNames ns (.embed c)) ∧
      c = Extended.frameProcess (state.frame.mapNames e) (state.body.mapNames e k) ∧
      Agent.Tau (state.body.mapNames e k) q ∧
      b.Interprets NameAssignment.literal (state.frame.mapNames e).value q :=
  h.fresh_canonical_interpretation state ha avoid

abbrev falseGuard : Formula Empty := .equal (.name 40) (.name 41)
abbrev falseBranch : Extended Empty := .plain (.branch falseGuard good bad)

theorem false_guard_takes_else : Extended.Reduction falseBranch (.plain bad) :=
  .elseBranch falseGuard good bad (by intro h; have he := (EqE.name_iff 40 41).mp h; cases he)

theorem fresh_false_conditional_retains_actual_target :
    ∃ q, Agent.Tau (.branch (.equal (.name 100) (.name 41)) (.output 8 (.name 100) .nil) bad) q ∧
      (Named.restrictNames [.base 40] (.embed (.plain bad))).Interprets NameAssignment.literal Empty.elim q := by
  apply Named.Opens.prefix_reduction_realizes [.base 40] false_guard_takes_else
    NameAssignment.literal (.newName (.base 40) 100 (.embed falseBranch _) (by simp))
  · intro a b ha hb he; cases a <;> cases b <;> exact he
  · decide
  · exact Agent.EvalEq.refl _

theorem canonical_example_has_constructed_full_target :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty), Agent.Tau state.body q ∧
      (Named.restrictedState ∅ target).Interprets NameAssignment.literal
        (state.frame.mapNames e).value (q.mapNames e k) :=
  actual_canonical_conditional.canonical_tau state (.refl _)

abbrev quiet : ScopedState {40} 1 := ⟨state.frame,.nil⟩

theorem no_spurious_internal_action_through_arbitrary_structure
    (a b : Named (Fin 1)) (ha : Named.Structural (Named.restrictedState ∅ quiet) a) :
    ¬ Named.Reduction a b := by
  intro h
  obtain ⟨_,_,q,hq,_⟩ := h.canonical_tau quiet ha
  exact Agent.tau_nil_no_step q hq

end ExplainableCrypto.Helios.Symbolic.SourceOpeningComparisonSPOT
