import ExplainableCrypto.Helios.Symbolic.SourceRigidityPreservation
import ExplainableCrypto.Helios.Symbolic.SourceRigidityBoundary
import ExplainableCrypto.Helios.Symbolic.SourceFrameInput

namespace ExplainableCrypto.Helios.Symbolic.SourceLocalRigiditySPOT
open Historical General Source Extended

abbrev cycle : Extended Empty := .newVar (.active none (.var none))
abbrev groundAlias : Extended Empty := .newVar (.active none (.name 40))
abbrev emptyState : Extended Empty := .plain .nil

/-- The source Alias rule eliminates an independent ground value. -/
theorem independent_alias_normalizes : Structural groundAlias emptyState :=
  .alias (.name 40)

theorem independent_alias_is_rigid : groundAlias.Rigid Empty.elim :=
  (independent_alias_normalizes.rigid Empty.elim).mpr True.intro

/-- Both bodies have the same full, inhabited interpretation class. The
existential local value of the cycle disappears from that class. -/
theorem cycle_has_complete_empty_class : cycle.SameRealizations emptyState := by
  intro env p
  constructor
  · rintro ⟨m,_,hp⟩
    exact hp
  · intro hp
    exact ⟨.name 40,.refl _,hp⟩

theorem cycle_class_is_nonempty : cycle.Realizes Empty.elim .nil :=
  ⟨.name 40,.refl _,.refl _⟩

theorem cycle_is_currently_wellFormed : cycle.WellFormed :=
  ⟨⟨True.intro,rfl⟩,closed_empty _⟩

theorem cycle_has_two_distinct_local_solutions :
    (Extended.active (none : Option Empty) (.var none)).Satisfies (extendEnv Empty.elim (.name 40)) ∧
    (Extended.active (none : Option Empty) (.var none)).Satisfies (extendEnv Empty.elim (.name 41)) ∧
    ¬ EqE (.name 40 : Ground) (.name 41) := by
  refine ⟨.refl _,.refl _,?_⟩
  intro he
  have hn := (EqE.name_iff 40 41).mp he
  cases hn

theorem cycle_is_not_rigid : ¬ cycle.Rigid Empty.elim := by
  intro h
  obtain ⟨h40,h41,hne⟩ := cycle_has_two_distinct_local_solutions
  exact hne (h.1 (.name 40) (.name 41) h40 h41)

/-- Kernel-checked refutation of semantic-class-to-Structural normalization
in the Extended fragment, despite nonvacuity, scope and unique definitions. -/
theorem cycle_cannot_normalize_to_empty : ¬ Structural cycle emptyState := by
  intro h
  exact cycle_is_not_rigid ((h.rigid Empty.elim).mpr True.intro)

/-- The stronger joint opening still admits this embedded semantic pair.
This statement does not assert a Named.Structural separation theorem. -/
theorem embedded_cycle_has_joint_empty_partner : Named.JointOpening (.embed cycle) (.embed emptyState) :=
  Named.JointOpening.embed cycle_has_complete_empty_class cycle_class_is_nonempty

theorem wellFormed_inhabited_class_is_insufficient :
    ¬ (∀ a b : Extended Empty, a.WellFormed → b.WellFormed →
      (∃ env p, a.Realizes env p) → a.SameRealizations b → Structural a b) := by
  intro h
  exact cycle_cannot_normalize_to_empty (h cycle emptyState cycle_is_currently_wellFormed
    ⟨True.intro,closed_empty _⟩ ⟨Empty.elim,.nil,cycle_class_is_nonempty⟩ cycle_has_complete_empty_class)

abbrev guardSource : Extended Empty := .par groundAlias
  (.plain (.branch (.equal (.name 40) (.name 40)) .nil .nil))
abbrev guardTarget : Extended Empty := .par groundAlias (.plain .nil)

/-- A real conditional step retains the nontrivial ground-alias constraint. -/
theorem conditional_step_preserves_rigidity :
    Reduction guardSource guardTarget ∧ guardTarget.Rigid Empty.elim := by
  have h : Reduction guardSource guardTarget :=
    .parRight _ (.thenBranch (.equal (.name 40) (.name 40)) .nil .nil (.refl _))
  exact ⟨h,(h.rigid Empty.elim).mp (fun _ _ => ⟨independent_alias_is_rigid,True.intro⟩)⟩

abbrev publicFrame : Frame ∅ 1 := ⟨fun _ => .name 42⟩
abbrev waiting : Agent Empty := .input 8 (.output 9 (.var none) .nil)
abbrev padded : Extended (Fin 1) := .par (frameProcess publicFrame waiting) (.newVar (.active none (.var none)))

theorem complete_live_frame_does_not_repair_normalization :
    padded.WellFormed ∧ padded.SameRealizations (frameProcess publicFrame waiting) ∧
      ¬ Structural padded (frameProcess publicFrame waiting) :=
  ⟨frame_with_unconstrained_local_wellFormed publicFrame waiting,
    frame_with_unconstrained_local_sameRealizations publicFrame waiting,
    frame_with_unconstrained_local_not_structural publicFrame waiting⟩

/-- The hidden self-reference does not make the complete process stuck:
its real public input still executes and retains the full frame and cycle. -/
theorem padded_process_has_actual_input :
    FreeStep padded (.input 8 (.var 0))
      (.par (frameProcess publicFrame (.output 9 (.name 42) .nil)) (.newVar (.active none (.var none)))) := by
  apply FreeStep.parLeft
  exact frame_visible_input_derivable publicFrame (.var 0)
    (.of_core (.input 8 (.name 42) (.output 9 (.var none) .nil)))

end ExplainableCrypto.Helios.Symbolic.SourceLocalRigiditySPOT
