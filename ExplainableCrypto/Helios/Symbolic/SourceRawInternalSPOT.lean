import ExplainableCrypto.Helios.Symbolic.SourceRawInternalMatching
import ExplainableCrypto.Helios.Symbolic.SourceLocalNormalizationSPOT
import ExplainableCrypto.Helios.Symbolic.SourceJointInternalSPOT
import ExplainableCrypto.Helios.Symbolic.SourceInputPresentationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceRawInternalSPOT
open Historical General Source

abbrev localGuard (accept : Bool) : Formula (Option (Fin 1)) :=
  if accept then .equal (.var none) (.var (some 0)) else .unequal (.var none) (.var (some 0))
abbrev localBody (accept : Bool) : Agent (Option (Fin 1)) :=
  .par (.branch (localGuard accept) (.output 8 (.var none) .nil) (.output 9 (.var none) .nil)) (.input 18 .nil)
abbrev localSource (accept : Bool) : Extended (Fin 1) := .newVar
  (.par (.active none (.name 40)) (.par (.active (some 0) (.var none)) (.plain (localBody accept))))
abbrev literalGuard (accept : Bool) : Formula Empty :=
  if accept then .equal (.name 40) (.name 40) else .unequal (.name 40) (.name 40)
abbrev literalBody (accept : Bool) : Agent Empty :=
  .par (.branch (literalGuard accept) (.output 8 (.name 40) .nil) (.output 9 (.name 40) .nil)) (.input 18 .nil)
abbrev literalAfter (accept : Bool) : Agent Empty := .par (.output (if accept then 8 else 9) (.name 40) .nil) (.input 18 .nil)
abbrev φ : Frame ∅ 1 := ⟨fun _ => .name 40⟩

private theorem local_normalizes (accept : Bool) :
    Extended.Structural (localSource accept) (Extended.frameProcess φ (literalBody accept)) := by
  have h := Extended.Structural.let_normalize (.name 40 : Term (Fin 1))
    (a := .par (.active (some 0) (.var none)) (.plain (localBody accept)))
    (by simp [Extended.Exports])
    (Extended.Instantiates.par (.active _ _ _ _ rfl) (.plain _ _))
  have hm := h.trans ((Extended.Structural.zero (.active 0 (.name 40))).symm.parLeft _)
  have hn := hm.trans (Extended.activeFrame_apply φ _)
  cases accept <;> exact hn

private theorem literal_tau (accept : Bool) : Agent.Tau (literalBody accept) (literalAfter accept) := by
  cases accept
  · exact (Agent.Tau.of_core (.elseBranch (literalGuard false) _ _ (fun h => h (.refl _)))).parLeft _
  · exact (Agent.Tau.of_core (.thenBranch (literalGuard true) _ _ (.refl _))).parLeft _

/-- The guard compares a local against a public provider that depends on that
local. Both truth values produce an original raw action and their literal
expected continuation, rather than a stuck existential witness. -/
theorem local_guard_has_actual_step (accept : Bool) :
    ∃ b, Named.Reduction (.embed (localSource accept)) b ∧
      Named.JointOpening b (Named.restrictedState ∅ (⟨φ,literalAfter accept⟩ : ScopedState ∅ 1)) := by
  have hs := local_normalizes accept
  have hp : (localSource accept).frameOf.BinderStructural (Extended.activeFrame φ) :=
    hs.frameOf.binderStructural.trans (Extended.frameProcess_frameOf φ (literalBody accept)).binderStructural
  have ha := (hs.realizes φ.value (literalBody accept)).mpr (Extended.frameProcess_realizes φ _)
  obtain ⟨b,hb⟩ := Extended.internal_available_of_presentation hp ha (literal_tau accept)
  have hj : Named.JointOpening (.embed (localSource accept))
      (Named.restrictedState ∅ (⟨φ,literalBody accept⟩ : ScopedState ∅ 1)) :=
    by
      apply (Named.restrictedState_jointOpening _).structural_left
      simpa only [Named.restrictedState,Named.restrictionNames,Finset.toList_empty,List.map_nil,
        List.append_nil,Named.restrictNames,List.foldr_nil] using (Named.Structural.embed hs).symm
  refine ⟨b,hb,hj.internal hb ?_⟩
  intro q hq
  exact .of_parEq (Agent.tau_branch_input_deterministic hq (literal_tau accept))

theorem local_then_and_else_choose_distinct_channels :
    ¬ Agent.EvalEq (literalAfter true) (literalAfter false) := by
  intro h
  have hh := h.hasOutput 8
  simp [Agent.HasOutput] at hh

/-- The original cyclic semantic shortcut still cannot supply the current
presentation required by internal availability. -/
theorem cyclic_semantic_partner_still_excluded (ψ : Frame ∅ 1) (hidden : Finset Nat) :
    ¬ (Named.embed (.par (Extended.frameProcess φ (literalBody true))
      (.newVar (.active none (.var none))))).RepresentsFrame hidden ψ :=
  Named.frame_with_unconstrained_local_no_presentation φ _ ψ hidden

open SourceJointInternalSPOT in
theorem private_raw_communication_available :
    ∃ b, Named.Reduction (.par (Named.restrictedState {18} privateSource) (.embed (.plain .nil))) b := by
  have hj := (Named.restrictedState_jointOpening (hidden := {18}) privateSource).structural_left
    (Named.Structural.zero _).symm
  exact hj.communication_available (c := 18) (by simp [Agent.HasOutput]) (by simp [Agent.HasInput])

/-- Each communication head lies under its own live local scope. The sender's
continuation remains private; the receiver retains the complete received term. -/
theorem communication_across_two_local_scopes :
    ∃ b, Extended.Reduction
      (.par
        (.newVar (.par (.active none (.name 40))
          (.plain (.output 18 (.var none) (.output 18 (.name 41) .nil)))))
        (.newVar (.par (.active none (.name 42))
          (.plain (.input 18 (.output 8 (.var none) .nil)))))) (b : Extended (Fin 0)) := by
  have ho := Extended.Structural.let_normalize (.name 40 : Term (Fin 0))
    (a := .plain (.output 18 (.var none) (.output 18 (.name 41) .nil)))
    (by simp [Extended.Exports]) (.plain _ _)
  have hi := Extended.Structural.let_normalize (.name 42 : Term (Fin 0))
    (a := .plain (.input 18 (.output 8 (.var none) .nil)))
    (by simp [Extended.Exports]) (.plain _ _)
  have hs := (ho.parLeft _).trans (hi.parRight _)
  have ha : (Extended.par
      (.plain (.output 18 (.name 40) (.output 18 (.name 41) .nil)))
      (.plain (.input 18 (.output 8 (.var none) .nil)))).Realizes Fin.elim0
      (.par (.output 18 (.name 40) (.output 18 (.name 41) .nil))
        (.input 18 (.output 8 (.var none) .nil))) := ⟨_,_,.refl _,.refl _,.refl _⟩
  exact Extended.communication_available_of_realizes ((hs.realizes _ _).mpr ha)
    (c := 18) (by simp [Agent.HasOutput]) (by simp [Agent.HasInput])

theorem different_channels_cannot_communicate :
    ¬ ∃ q, Agent.Tau (.par (.output 8 (.name 40) .nil) (.input 9 .nil)) q := by
  rintro ⟨q,hq⟩
  exact Agent.tau_output_input_no_step (by decide) hq

open SourceCoordinatedSPOT

/-- A real component replay is rejected in both vote worlds; matching builds
an action from a padded raw partner, with complete successor observations. -/
theorem actual_replay_rejection_matches_raw_partner (swap swap' : Bool) :
    ∃ (next : Process.Phase) (hh : 3 = next.handles) (t : Named (Fin 3)), Named.Reduction
      (.par (SourceReachableElectionSPOT.raw swap' (.check [] (.var 1))) (.embed (.plain .nil))) t ∧
      Named.StaticEq ((SourceReachableElectionSPOT.raw swap (.rejected [])).rename (Fin.cast hh))
        (t.rename (Fin.cast hh)) := by
  let a := SourceReachableElectionSPOT.raw swap (.check [] (.var 1))
  let d := SourceReachableElectionSPOT.raw swap' (.check [] (.var 1))
  have ha : Named.JointOpening a (Named.mappedState ch.privateChannels
      (sourceState ns swap left right 1 ch (.check [] (.var 1))) (Equiv.refl Nat) (Equiv.refl Nat)) := by
    simpa only [Named.mappedState_identity] using Named.restrictedState_jointOpening
      (hidden := ch.privateChannels) (sourceState ns swap left right 1 ch (.check [] (.var 1)))
  have hd : Named.JointOpening d (Named.mappedState ch.privateChannels
      (sourceState ns swap' left right 1 ch (.check [] (.var 1))) (Equiv.refl Nat) (Equiv.refl Nat)) := by
    simpa only [Named.mappedState_identity] using Named.restrictedState_jointOpening
      (hidden := ch.privateChannels) (sourceState ns swap' left right 1 ch (.check [] (.var 1)))
  have present (sw : Bool) : (SourceReachableElectionSPOT.raw sw (.check [] (.var 1))).RepresentsFrame
      (ch.privateChannels.image (Equiv.refl Nat)) ((sourceView ns sw left right (.check [] (.var 1))).mapNames (Equiv.refl Nat)) := by
    have hs : Named.Structural (SourceReachableElectionSPOT.raw sw (.check [] (.var 1)))
        (Named.mappedState ch.privateChannels (sourceState ns sw left right 1 ch (.check [] (.var 1)))
          (Equiv.refl Nat) (Equiv.refl Nat)) := by
      rw [Named.mappedState_identity]
      exact .refl _
    exact (Named.restrictedState_represents (hidden := ch.privateChannels)
      (sourceState ns sw left right 1 ch (.check [] (.var 1)))).transport_state_structure hs
  obtain ⟨next,hh,t,ht,_,_,_,_,_,_,he⟩ := source_reachable_internal_match ns
    NumericReflectionSPOT.fixture_names_fresh swap swap' left right 1 ch Channels.canonical_fresh
    (Equiv.refl Nat) (Equiv.refl Nat) (.check [] (.var 1))
    ((waiting_phase_is_reached swap).tail ⟨.input 2 (.var 1),.input (by decide) trivial⟩)
    ha (hd.structural_left (Named.Structural.zero _).symm) (present swap)
    ((present swap').structural (Named.Structural.zero _).symm)
    (SourceReachableElectionSPOT.actual_replay_rejection swap)
  exact ⟨next,hh,t,ht,he⟩

end ExplainableCrypto.Helios.Symbolic.SourceRawInternalSPOT
