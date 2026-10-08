import ExplainableCrypto.Helios.Symbolic.SourceCanonicalBodyInterpretation
import ExplainableCrypto.Helios.Symbolic.SourceNameInterpretationSPOT
import ExplainableCrypto.Helios.Symbolic.SourceProcessSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNamedBodySPOT
open Historical General Source
variable {restricted hidden : Finset Nat} {handles n : Nat}

theorem base_update_preserves_same_numeral_channel :
    (Function.update NameAssignment.literal (.base 8) 40) (.base 8) = 40 ∧
    (Function.update NameAssignment.literal (.base 8) 40) (.channel 8) = 8 := by decide

theorem channel_update_preserves_same_numeral_base :
    (Function.update NameAssignment.literal (.channel 8) 18) (.channel 8) = 18 ∧
    (Function.update NameAssignment.literal (.channel 8) 18) (.base 8) = 8 := by decide

abbrev code (n : Nat) : Extended (Fin 1) :=
  .par (.active 0 (.name n)) (.plain (.output 8 (.name n) .nil))
abbrev boundCode (n : Nat) : Named (Fin 1) := .newName (.base n) (.embed (code n))
abbrev observed : Agent Empty := .par .nil (.output 8 (.name 40) .nil)

theorem original_frame_and_body :
    (boundCode 40).Interprets NameAssignment.literal (fun _ => .name 40) observed :=
  ⟨40,.nil,.output 8 (.name 40) .nil,⟨.refl _,.refl _⟩,.refl _,.refl _⟩

theorem actual_alpha_moves_frame_and_code : Named.Structural (boundCode 40) (boundCode 50) := by
  simpa only [boundCode,code,Named.mapNames,Extended.mapNames,Term.mapNames,
    Agent.mapNames,Equiv.swap_apply_left,id_eq] using
    Named.Structural.alphaBase (.embed (code 40)) 40 50 (by decide)

theorem alpha_preserves_every_full_interpretation (ρ : NameAssignment)
    (env : Fin 1 → Ground) (p : Agent Empty) :
    (boundCode 40).Interprets ρ env p ↔ (boundCode 50).Interprets ρ env p :=
  actual_alpha_moves_frame_and_code.interprets ρ env p

theorem renamed_code_interprets_original_environment_and_body :
    (boundCode 50).Interprets NameAssignment.literal (fun _ => .name 40) observed :=
  (alpha_preserves_every_full_interpretation _ _ _).mp original_frame_and_body

theorem free_frame_rejects_stale_environment (p : Agent Empty) :
    ¬ (Named.embed (code 50)).Interprets NameAssignment.literal (fun _ => .name 40) p := by
  rintro ⟨q,r,⟨he,_⟩,_,_⟩
  exact (by decide : (40 : Nat) ≠ 50) ((EqE.name_iff 40 50).mp he)

abbrev fullProof : Ground := .spk (.name 1) (.name 2) (.const .one) (.name 99)

theorem full_fourth_field_retained_in_frame_and_output :
    (Named.embed (.par (.active (0 : Fin 1)
      (.spk (.name 1) (.name 2) (.const .one) (.name 99)))
      (.plain (.output 8 (.spk (.name 1) (.name 2) (.const .one) (.name 99)) .nil)))).Interprets NameAssignment.literal (fun _ => fullProof)
        (.par .nil (.output 8 fullProof .nil)) :=
  ⟨.nil,.output 8 fullProof .nil,⟨.refl _,.refl _⟩,.refl _,.refl _⟩

abbrev localFutureInput : Named Empty := .newVar (.par
  (.embed (.active none (.name 40)))
  (.embed (.plain (.input 12 (.output 13
    (.binary .pair (.var (some none)) (.var none)) .nil)))))

theorem local_value_does_not_capture_future_input :
    localFutureInput.Interprets NameAssignment.literal Empty.elim
      (.par .nil (.input 12 (.output 13 (.binary .pair (.name 40) (.var none)) .nil))) :=
  ⟨.name 40,.nil,.input 12 (.output 13 (.binary .pair (.name 40) (.var none)) .nil),
    ⟨.refl _,.refl _⟩,.refl _,.refl _⟩

abbrev distinctGuard : Formula Empty := .unequal (.name 40) (.name 41)

theorem distinct_name_guard_holds : distinctGuard.Holds Empty.elim := by
  intro h
  exact (by decide : (40 : Nat) ≠ 41) ((EqE.name_iff 40 41).mp h)

theorem collapsing_names_falsifies_guard :
    ¬ (distinctGuard.mapNames (fun _ => 0)).Holds Empty.elim := fun h => h (.refl _)

theorem collapsing_names_changes_branch :
    Agent.CoreStep (.branch distinctGuard (.output 9 (.const .one) .nil) .nil)
      (.output 9 (.const .one) .nil) ∧
    Agent.CoreStep ((Agent.branch distinctGuard (.output 9 (.const .one) .nil) .nil).mapNames
      (fun _ => 0) id) .nil :=
  ⟨.thenBranch _ _ _ distinct_name_guard_holds,.elseBranch _ _ _ collapsing_names_falsifies_guard⟩

abbrev wrongChannels : Agent Empty :=
  .par (.output 8 (.name 40) .nil) (.input 10 (.output 9 (.var none) .nil))

theorem original_channels_cannot_communicate (p : Agent Empty) :
    ¬ Agent.CoreStep wrongChannels p := SourceProcessSPOT.wrong_channel_cannot_communicate p

theorem collapsing_channels_creates_communication :
    Agent.CoreStep (wrongChannels.mapNames id (fun _ => 0))
      (.par .nil (.output 0 (.name 40) .nil)) := .comm _ _ _ _

theorem interpretation_admits_collapsed_communicating_body :
    (Named.embed (.plain wrongChannels)).Interprets
      (fun n => match n with | .base k => k | .channel _ => 0) Empty.elim
        (wrongChannels.mapNames id (fun _ => 0)) := by
  change Agent.EvalEq _ _
  exact .refl _

theorem all_election_states_interpret_full_body (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (phase : Process.Phase) :
    (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)).Interprets
      NameAssignment.literal (sourceView ns swap left right phase).value
      (residual ns swap left right extra ch phase) := Named.restrictedState_interprets _

theorem arbitrary_structural_representative_keeps_full_body
    (s : ScopedState restricted handles) (a : Named (Fin handles))
    (h : Named.Structural (Named.restrictedState hidden s) a) :
    a.Interprets NameAssignment.literal s.frame.value s.body := h.canonical_interprets s

theorem fresh_prenex_representation_keeps_full_body (s : ScopedState restricted handles)
    (avoid : Finset SourceName) :
    ∃ ns a, Named.Structural (Named.restrictedState hidden s) (Named.restrictNames ns (.embed a)) ∧
      ns.Nodup ∧ (∀ n ∈ ns, n ∉ avoid) ∧
      ∃ τ : NameAssignment, (∀ n, n ∉ ns → τ n = NameAssignment.literal n) ∧
        (a.mapNames τ.base τ.channel).Realizes s.frame.value s.body := by
  obtain ⟨ns,a,h,hn,hf⟩ := Named.exists_distinct_fresh_prenex (Named.restrictedState hidden s) avoid
  exact ⟨ns,a,h,hn,hf,h.canonical_prenex_interprets s ns a⟩

theorem no_name_prefix_keeps_every_assignment (a : Extended (Fin 1))
    (ρ : NameAssignment) (env : Fin 1 → Ground) (p : Agent Empty)
    (h : (Named.restrictNames [] (.embed a)).Interprets ρ env p) :
    (a.mapNames ρ.base ρ.channel).Realizes env p := h

end ExplainableCrypto.Helios.Symbolic.SourceNamedBodySPOT
