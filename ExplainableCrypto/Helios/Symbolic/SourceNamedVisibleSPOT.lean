import ExplainableCrypto.Helios.Symbolic.SourceFiniteFaithfulAssignments
import ExplainableCrypto.Helios.Symbolic.SourceNamedBodySPOT
import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionSPOT
import ExplainableCrypto.Helios.Symbolic.SourceNamedStaticSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNamedVisibleSPOT
open Historical General Source

abbrev alphaAfter : Named (Fin 1) := .newName (.base 41) (.embed
  (.par (.active 0 (.unary .pk (.name 41))) (.plain (.output 0 (.name 40) .nil))))

/-- The old literal remains unchanged through an actual alpha-closed input.
Its apparent collision with the interpreted key is not evidence of publicness. -/
theorem old_literal_input_has_full_interpretation :
    ∃ q, Agent.Visible (.input 0 (.output 0 (.var none) .nil)) (.input 0 (.name 40)) q ∧
      alphaAfter.Interprets NameAssignment.literal (fun _ => .unary .pk (.name 40)) q := by
  apply SourceInputAlphaBoundary.old_literal_input_after_alpha.input_interprets
    (fun _ => .unary .pk (.name 40))
  exact ⟨40,.nil,.input 0 (.output 0 (.var none) .nil),⟨.refl _,.refl _⟩,.refl _,
    .of_parEq (.zero_left _)⟩

theorem old_literal_still_fails_original_policy :
    ¬ (Term.name 40 : Recipe 1).Public {40} := by simp [Term.Public]

theorem interpreted_alpha_target_keeps_complete_key_and_input :
    alphaAfter.Interprets NameAssignment.literal (fun _ => .unary .pk (.name 40))
      (.output 0 (.name 40) .nil) :=
  ⟨40,.nil,.output 0 (.name 40) .nil,⟨.refl _,.refl _⟩,.refl _,.of_parEq (.zero_left _)⟩

theorem actual_voter_input_classifies (swap : Bool) :
    (Named.restrictedState Channels.canonical.privateChannels
      (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        1 Channels.canonical (.check [] (.var 1)))).Interprets NameAssignment.literal
      (SharedTallySPOT.world swap).value
      (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        1 Channels.canonical (.check [] (.var 1))) := by
  obtain ⟨rs,he,_,r,hr,hb⟩ := source_named_canonical_input SharedTallySPOT.names swap
    SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.input []) (by exact Nat.zero_lt_succ 0)
    (SourceNameRestrictionSPOT.actual_voter_input_has_name_scope swap)
  cases he
  obtain rfl := eq_of_heq hr
  exact hb

theorem actual_voter_input_keeps_frame_presentation (swap : Bool) :
    ∃ q : ScopedState SharedTallySPOT.names.restricted 3,
      ScopedStep Channels.canonical.privateChannels SharedTallySPOT.names.restricted
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
          1 Channels.canonical (.input [])) (.input 4 (.var (1 : Fin 3))) q ∧
      q.frame = SharedTallySPOT.world swap ∧
      (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
          1 Channels.canonical (.check [] (.var 1)))).RepresentsFrame
          Channels.canonical.privateChannels q.frame := by
  obtain ⟨q,hq,hf,_,hp⟩ := (SourceNameRestrictionSPOT.actual_voter_input_has_name_scope swap).canonical_input_scoped (sourceState SharedTallySPOT.names swap SharedTallySPOT.left
      SharedTallySPOT.right 1 Channels.canonical (.input [])) trivial
  exact ⟨q,hq,hf,hp⟩

theorem actual_output_keeps_complete_fourth_field :
    ∃ q, Agent.Visible SourceNamedStaticSPOT.p.body (.output 0 SourceVisibleInterpretationSPOT.proofPayload) q ∧
      (Named.restrictedCapture ∅ SourceNamedStaticSPOT.p.frame SourceVisibleInterpretationSPOT.proofPayload .nil).Interprets NameAssignment.literal
          (extendEnv SourceNamedStaticSPOT.p.frame.value SourceVisibleInterpretationSPOT.proofPayload) q := by
  obtain ⟨m,q,hq,hb,_⟩ := SourceNamedStaticSPOT.static_clause_does_not_supply_dynamic_matching.2.1.canonical_output SourceNamedStaticSPOT.p
  obtain ⟨body,hm⟩ := hq.output_prefix
  simp only [Agent.threads,Agent.threadList,Multiset.mem_coe,List.mem_singleton,Agent.output.injEq,
    true_and] at hm
  obtain ⟨rfl,_⟩ := hm
  exact ⟨q,hq,hb⟩

theorem stopped_body_has_no_named_output (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput (Named.restrictedState ∅ SourceNamedStaticSPOT.stop) 0 b := by
  intro h
  obtain ⟨m,q,hq,_,_⟩ := h.canonical_output SourceNamedStaticSPOT.stop
  obtain ⟨body,hm⟩ := hq.output_prefix
  simp [Agent.threads,Agent.threadList] at hm

theorem rejected_election_has_no_named_input (swap : Bool) (c : Nat) (r : Recipe 3)
    (b : Named (Fin 3)) :
    ¬ Named.FreeStep (Named.restrictedState Channels.canonical.privateChannels
      (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        1 Channels.canonical (.rejected []))) (.input c r) b := by
  intro h
  obtain ⟨rs,he,_⟩ := source_named_canonical_input SharedTallySPOT.names swap
    SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.rejected []) (by simp [Process.Phase.inRange]) h
  cases he

theorem rejected_election_has_no_named_output (swap : Bool) (c : Nat)
    (b : Named (Option (Fin 3))) :
    ¬ Named.BoundOutput (Named.restrictedState Channels.canonical.privateChannels
      (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        1 Channels.canonical (.rejected []))) c b := by
  intro h
  obtain ⟨handle,m,next,hp,_⟩ := source_named_canonical_output SharedTallySPOT.names swap
    SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical (.rejected []) (by simp [Process.Phase.inRange]) h
  cases hp

theorem first_publication_has_exact_ballot_and_continuation (swap : Bool)
    (b : Named (Option (Fin 1))) (c : Nat)
    (h : Named.BoundOutput (Named.restrictedState Channels.canonical.privateChannels
      (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        0 Channels.canonical .firstReceived)) c b) :
    c = 0 ∧ b.Interprets NameAssignment.literal
      (extendEnv (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .firstReceived).value
        (ballot SharedTallySPOT.names 0 (choice swap SharedTallySPOT.left SharedTallySPOT.right 0).value))
      (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
        0 Channels.canonical .firstPublished) := by
  obtain ⟨handle,m,next,hp,hc,_,_,hb,_⟩ := source_named_canonical_output SharedTallySPOT.names swap
    SharedTallySPOT.left SharedTallySPOT.right 0 Channels.canonical .firstReceived trivial h
  cases hp
  exact ⟨hc,hb⟩

theorem first_publication_exists_with_interpreted_continuation (swap : Bool) :
    ∃ b : Named (Option (Fin 1)),
      Named.BoundOutput (Named.restrictedState Channels.canonical.privateChannels
        (sourceState SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
          0 Channels.canonical .firstReceived)) 0 b ∧
      b.Interprets NameAssignment.literal
        (extendEnv (sourceView SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right .firstReceived).value
          (ballot SharedTallySPOT.names 0 (choice swap SharedTallySPOT.left SharedTallySPOT.right 0).value))
        (residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right
          0 Channels.canonical .firstPublished) := by
  have hp := (Publication.first (ns := SharedTallySPOT.names) (swap := swap)
    (left := SharedTallySPOT.left) (right := SharedTallySPOT.right) (extra := 0)).scoped
      Channels.canonical Channels.canonical_fresh
  obtain ⟨m,hb,_⟩ := Named.restricted_output_derivable _ _ _ hp.1
  exact ⟨_,hb,(first_publication_has_exact_ballot_and_continuation swap _ _ hb).2⟩

abbrev alphaAssignment : NameAssignment := Function.update NameAssignment.literal (.base 50) 40

theorem alpha_assignment_faithful_on_used_names :
    alphaAssignment.FaithfulOn {SourceName.base 50,SourceName.channel 8} := by
  intro a b ha hb he
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | cases he

theorem same_numeral_different_sorts_are_faithful :
    NameAssignment.FaithfulOn (fun _ => 0) {SourceName.base 8,SourceName.channel 8} := by
  intro a b ha hb he
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | cases he

theorem finite_assignment_has_permutation_extensions :
    ∃ e k : Nat ≃ Nat, e 50 = 40 ∧ k 8 = 8 := by
  obtain ⟨e,k,he,hk⟩ := alpha_assignment_faithful_on_used_names.exists_permutations
  exact ⟨e,k,he 50 (by simp),hk 8 (by simp)⟩

theorem alpha_assignment_is_not_globally_injective :
    ¬ Function.Injective alphaAssignment.base := by
  intro h
  have he : (50 : Nat) = 40 := h (by decide)
  omega

/-- Global injectivity plus fixing all names outside the new prefix would
exclude this legitimate interpretation of an alpha-renamed private frame. -/
theorem no_globally_injective_fixed_prefix_witness :
    ¬ ∃ ρ : NameAssignment,
      (∀ n, n ∉ [SourceName.base 50] → ρ n = NameAssignment.literal n) ∧
      Function.Injective ρ.base ∧
      ((Extended.active (0 : Fin 1) (.name 50)).mapNames ρ.base ρ.channel).Realizes
        (fun _ => .name 40) .nil := by
  rintro ⟨ρ,hfix,hi,he,_⟩
  have h50 : ρ.base 50 = 40 := ((EqE.name_iff 40 (ρ.base 50)).mp he).symm
  have h40 : ρ.base 40 = 40 := hfix (.base 40) (by decide)
  have heq : (50 : Nat) = 40 := hi (h50.trans h40.symm)
  omega

theorem collapsed_channels_fail_faithfulness :
    ¬ NameAssignment.FaithfulOn (fun _ => 0)
      {SourceName.channel 8,SourceName.channel 10} := by
  intro h
  have he := h (a := .channel 8) (b := .channel 10) (by simp) (by simp) rfl
  cases he

theorem guard_collision_still_changes_branch :
    SourceNamedBodySPOT.distinctGuard.Holds Empty.elim ∧
      ¬ (SourceNamedBodySPOT.distinctGuard.mapNames (fun _ => 0)).Holds Empty.elim :=
  ⟨SourceNamedBodySPOT.distinct_name_guard_holds,SourceNamedBodySPOT.collapsing_names_falsifies_guard⟩

theorem internal_transport_uses_only_finite_support (a b : Extended (Fin 1))
    (h : Extended.Reduction a b)
    (hf : alphaAssignment.FaithfulOn (a.nameSupport ∪ b.nameSupport)) :
    Extended.Reduction (a.mapNames alphaAssignment.base alphaAssignment.channel)
      (b.mapNames alphaAssignment.base alphaAssignment.channel) :=
  (Extended.reduction_mapAssignments_iff a b alphaAssignment hf).mpr h

abbrev expandedBinding : Extended (Fin 1) :=
  .active 0 (.unary .fst (.binary .pair (.name 50) (.name 40)))

theorem discarded_field_is_an_actual_source_rewrite :
    Named.Structural (.newName (.base 50) (.embed (.active (0 : Fin 1) (.name 50))))
      (.newName (.base 50) (.embed expandedBinding)) :=
  .newName _ (.embed (.rewrite _ (EqE.equation (.fst _ _)).symm))

theorem discarded_field_keeps_literal_interpretation :
    (Named.newName (.base 50) (.embed expandedBinding)).Interprets NameAssignment.literal
      (fun _ => .name 40) .nil :=
  (discarded_field_is_an_actual_source_rewrite.interprets _ _ _).mp ⟨40,.refl _,.refl _⟩

/-- Even injectivity on the raw syntactic support can be too strong for a
fixed old environment: full E may introduce the old literal in a dead field. -/
theorem discarded_field_blocks_faithful_fixed_environment :
    ¬ ∃ ρ : NameAssignment,
      (∀ n, n ∉ [SourceName.base 50] → ρ n = NameAssignment.literal n) ∧
      ρ.FaithfulOn expandedBinding.nameSupport ∧
      (expandedBinding.mapNames ρ.base ρ.channel).Realizes (fun _ => .name 40) .nil := by
  rintro ⟨ρ,hfix,hf,he,_⟩
  have h50 : ρ.base 50 = 40 := ((EqE.name_iff 40 (ρ.base 50)).mp
    (he.trans (EqE.equation (.fst _ _)))).symm
  have h40 : ρ.base 40 = 40 := hfix (.base 40) (by decide)
  have heq := hf (a := .base 50) (b := .base 40) (by decide) (by decide)
    (congrArg SourceName.base (h50.trans h40.symm))
  cases heq

end ExplainableCrypto.Helios.Symbolic.SourceNamedVisibleSPOT
