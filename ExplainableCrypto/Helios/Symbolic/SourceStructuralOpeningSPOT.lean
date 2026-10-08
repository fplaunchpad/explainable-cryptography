import ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningReconstruction
import ExplainableCrypto.Helios.Symbolic.SourceBoundRigiditySPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningSPOT
open Historical General Source

abbrev inputBody : Extended Empty := .plain (.input 7 .nil)
abbrev leftUnused : Named Empty := .newName (.base 70) (.embed inputBody)
abbrev rightUnused : Named Empty := .newName (.channel 80) (.newName (.base 81) (.embed inputBody))

theorem left_unused_opening :
    Named.Opens leftUnused NameAssignment.literal [.base 100] inputBody :=
  .newName (.base 70) 100 (.embed _ _) (by decide)

theorem right_unused_opening :
    Named.Opens rightUnused NameAssignment.literal [.channel 108,.base 109] inputBody :=
  .newName (.channel 80) 108 (.newName (.base 81) 109 (.embed _ _) (by decide)) (by decide)

theorem unequal_prefix_lengths_reconstruct : Named.Structural leftUnused rightUnused :=
  left_unused_opening.structural_of_binder right_unused_opening (by decide) (by decide) (.refl _)

theorem reconstruction_retains_live_input :
    Named.FreeStep leftUnused (.input 7 (.name 42)) (.newName (.base 70) (.embed (.plain .nil))) :=
  .scopeName (.base 70) (by decide) (.embed (.input 7 (.name 42) .nil))

theorem converse_refreshes_beyond_both_allocations :
    ∃ ns b ms c,
      Named.Opens leftUnused NameAssignment.literal ns b ∧
      Named.Opens rightUnused NameAssignment.literal ms c ∧
      (∀ n ∈ ns, n ∉ ({.base 100,.channel 108,.base 109} : Finset SourceName) ∪
        (leftUnused.allNames ∪ rightUnused.allNames)) ∧
      (∀ n ∈ ms, n ∉ ({.base 100,.channel 108,.base 109} : Finset SourceName) ∪
        (leftUnused.allNames ∪ rightUnused.allNames)) ∧ b.BinderStructural c :=
  unequal_prefix_lengths_reconstruct.fresh_binder_openings _

abbrev privateProvider (n : Nat) : Named (Fin 1) := .newName (.base n) (.embed (.active 0 (.name n)))

theorem used_private_names_reconstruct : Named.Structural (privateProvider 40) (privateProvider 41) := by
  have ha : Named.Opens (privateProvider 40) NameAssignment.literal [.base 100] (.active 0 (.name 100)) :=
    .newName (.base 40) 100 (.embed _ _) (by decide)
  have hb : Named.Opens (privateProvider 41) NameAssignment.literal [.base 100] (.active 0 (.name 100)) :=
    .newName (.base 41) 100 (.embed _ _) (by decide)
  exact ha.structural_of_binder hb (by decide) (by decide) (.refl _)

theorem dependent_variable_exchange_reconstructs :
    Named.Structural
      (.newName (.base 70) (.embed SourceBoundRigiditySPOT.dependentLocals))
      (.newName (.channel 80) (.embed (.newVar (.newVar
        (SourceBoundRigiditySPOT.dependentBody.rename Extended.swapBinders))))) := by
  have ha : Named.Opens
      (.newName (.base 70) (.embed SourceBoundRigiditySPOT.dependentLocals))
      NameAssignment.literal [.base 100] SourceBoundRigiditySPOT.dependentLocals :=
    .newName (.base 70) 100 (.embed _ _) (by decide)
  have hb : Named.Opens
      (.newName (.channel 80) (.embed (.newVar (.newVar
        (SourceBoundRigiditySPOT.dependentBody.rename Extended.swapBinders)))))
      NameAssignment.literal [.channel 108] (.newVar (.newVar
        (SourceBoundRigiditySPOT.dependentBody.rename Extended.swapBinders))) :=
    .newName (.channel 80) 108 (.embed _ _) (by decide)
  exact ha.structural_of_binder hb (by decide) (by decide) (.varComm _)

abbrev hiddenInput : Named Empty := .newName (.channel 7) (.embed inputBody)

theorem collision_opening_has_identical_body :
    Named.Opens hiddenInput NameAssignment.literal [.channel 7] inputBody :=
  .newName (.channel 7) 7 (.embed _ _) (by decide)

theorem collision_fails_joint_freshness :
    ¬ (∀ n ∈ ([.channel 7] : List SourceName),
      n ∉ hiddenInput.allNames ∪ (Named.embed inputBody).allNames) := by decide

theorem dropping_freshness_cannot_reconstruct :
    ¬ Named.Structural hiddenInput (.embed inputBody) := by
  intro h
  have hc := h.channels
  exact (by decide : hiddenInput.channels ≠ (Named.embed inputBody).channels) hc

theorem semantic_equality_is_insufficient :
    SourceLocalRigiditySPOT.cycle.SameRealizations SourceLocalRigiditySPOT.emptyState ∧
    ¬ Named.Structural (.embed SourceLocalRigiditySPOT.cycle) (.embed SourceLocalRigiditySPOT.emptyState) :=
  ⟨SourceLocalRigiditySPOT.cycle_has_complete_empty_class,Named.unconstrained_local_not_structural⟩

theorem insufficient_semantic_pair_is_inhabited :
    SourceLocalRigiditySPOT.cycle.Realizes Empty.elim .nil :=
  SourceLocalRigiditySPOT.cycle_class_is_nonempty

abbrev payload : Ground := .spk (.name 42) (.name 43) (.const .one) (.name 99)
abbrev echoBody : Extended Empty := .plain (.input 7 (.output 9 (.var none) .nil))
abbrev echoSource : Named Empty := .newName (.base 40) (.embed echoBody)
abbrev echoTarget : Named Empty := .newName (.base 40) (.embed (.plain (.output 9 payload .nil)))

theorem full_label_input_opens_to_actual_action :
    ∃ ms b, Named.Opens echoTarget NameAssignment.literal ms b ∧
      Named.FreeStep (.embed echoBody) (.input 7 payload) (.embed b) ∧
      (∀ n ∈ ms, n ∉ ({.base 900,.channel 900} : Finset SourceName)) := by
  have hr : Named.FreeStep echoSource (.input 7 payload) echoTarget :=
    .scopeName (.base 40) (by decide) (.embed (.input 7 payload (.output 9 (.var none) .nil)))
  have ho : Named.Opens echoSource NameAssignment.literal [.base 100] echoBody :=
    .newName (.base 40) 100 (.embed _ _) (by decide)
  exact hr.opening_named_step _ ho (by decide)

theorem scoped_output_opens_to_actual_full_target :
    ∃ ms b,
      Named.Opens (.newName (.base 50) (.embed SourceVisibleInterpretationSPOT.scopedTarget))
        NameAssignment.literal ms b ∧
      Named.BoundOutput (.embed SourceVisibleInterpretationSPOT.scopedSource) 0 (.embed b) ∧
      (∀ n ∈ ms, n ∉ ({.base 900,.channel 900} : Finset SourceName)) := by
  have hr : Named.BoundOutput
      (.newName (.base 50) (.embed SourceVisibleInterpretationSPOT.scopedSource)) 0
      (.newName (.base 50) (.embed SourceVisibleInterpretationSPOT.scopedTarget)) :=
    .scopeName (.base 50) (by decide) (.embed SourceAtomicOutputSPOT.output_crosses_variable_scope)
  have ho : Named.Opens
      (.newName (.base 50) (.embed SourceVisibleInterpretationSPOT.scopedSource))
      NameAssignment.literal [.base 100] SourceVisibleInterpretationSPOT.scopedSource :=
    .newName (.base 50) 100 (.embed _ _) (by decide)
  exact hr.opening_named_step _ ho (by decide)

abbrev communicating : Extended (Fin 1) := .plain (.par (.output 7 (.var 0) .nil) (.input 7 .nil))
abbrev communicated : Extended (Fin 1) := .plain (.par .nil .nil)

theorem internal_communication_opens_to_actual_action :
    ∃ ns a ms b,
      Named.Opens (.newName (.base 50) (.embed communicating)) NameAssignment.literal ns a ∧
      Named.Opens (.newName (.base 50) (.embed communicated)) NameAssignment.literal ms b ∧
      Named.Reduction (.embed a) (.embed b) ∧
      (∀ n ∈ ns, n ∉ ({.base 900,.channel 900} : Finset SourceName)) ∧
      (∀ n ∈ ms, n ∉ ({.base 900,.channel 900} : Finset SourceName)) := by
  have hr : Named.Reduction (.newName (.base 50) (.embed communicating))
      (.newName (.base 50) (.embed communicated)) :=
    .newName (.base 50) (.embed (.atomComm 7 0 .nil .nil))
  obtain ⟨needed,ht⟩ := hr.opening_named_step
  obtain ⟨ns,a,ha,hf⟩ := Named.exists_fresh_opening _ NameAssignment.literal
    (({.base 900,.channel 900} : Finset SourceName) ∪ needed)
  obtain ⟨ms,b,hb,hs,hg⟩ := ht _ ns a ha hf
  exact ⟨ns,a,ms,b,ha,hb,hs,
    fun n hn hm => hf n hn (Finset.mem_union_left _ hm),
    fun n hn hm => hg n hn (Finset.mem_union_left _ hm)⟩

end ExplainableCrypto.Helios.Symbolic.SourceStructuralOpeningSPOT
