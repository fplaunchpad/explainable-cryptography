import ExplainableCrypto.Helios.Symbolic.SourceElectionVisibleInvariant
import ExplainableCrypto.Helios.Symbolic.SourceTargetInvariantSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceVisibleInvariantSPOT
open Historical General Source

abbrev φ : Frame {40} 1 := ⟨fun _ => .name 40⟩
abbrev payload : Ground := .spk (.name 40) (.name 41) (.const .one) (.name 99)
abbrev continuation : Agent Empty := .input 9 (.output 10 (.var none) .nil)
abbrev outputCode : Agent Empty := .output 8 payload continuation
abbrev capture : Extended (Option (Fin 1)) :=
  .par ((Extended.activeFrame φ).rename some)
    (Extended.capture (Extended.groundTerm payload) (Extended.groundAgent continuation))

theorem actual_full_output : Extended.BoundOutput (Extended.frameProcess φ outputCode) 8 capture :=
  Extended.frame_output_derivable φ 8 payload continuation

theorem full_output_is_deterministic (n : Ground) (q : Agent Empty)
    (h : Agent.Visible outputCode (.output 8 n) q) : EqE n payload ∧ Agent.EvalEq q continuation := by
  obtain ⟨body,hb⟩ := h.output_prefix
  simp [outputCode,Agent.threads,Agent.threadList] at hb
  obtain ⟨rfl,rfl⟩ := hb
  refine ⟨.refl _,.of_parEq (Agent.visible_output_deterministic h (.of_core (.output _ _ _)) ?_)⟩
  intro a b ha hb
  simp [outputCode,Agent.threads,Agent.threadList] at ha hb
  exact ha.trans hb.symm

theorem actual_capture_has_all_values : capture.Realizes (extendEnv φ.value payload) continuation := by
  exact (actual_full_output.capture_realizes_iff φ outputCode continuation payload (.refl _)
    full_output_is_deterministic _ _ _).mpr ⟨fun _ => .refl _,.refl _,.refl _⟩

theorem backward_output_retains_complete_value :
    ∃ p n q, (Extended.frameProcess φ outputCode).Realizes φ.value p ∧ EqE payload n ∧
      Agent.Visible p (.output 8 n) q ∧ Agent.EvalEq q continuation :=
  actual_full_output.realizes_backward φ.value payload actual_capture_has_all_values

theorem fresh_handle_has_complete_canonical_class :
    (capture.rename Extended.outputHandle).SameRealizations
      (Extended.frameProcess (φ.extend payload) continuation) :=
  actual_full_output.sameRealizations_target φ outputCode continuation payload (.refl _) full_output_is_deterministic

abbrev wrongFourth : Ground := .spk (.name 40) (.name 41) (.const .one) (.name 98)

theorem wrong_fourth_field_is_rejected (q : Agent Empty) :
    ¬ capture.Realizes (extendEnv φ.value wrongFourth) q := by
  intro h
  have hm := ((actual_full_output.capture_realizes_iff φ outputCode continuation payload (.refl _)
    full_output_is_deterministic _ _ _).mp h).2.1
  have he := (EqE.spk_iff _ _ _ _ _ _ _ _).mp hm
  have hn := (EqE.name_iff 98 99).mp he.2.2.2
  cases hn

theorem wrong_old_value_is_rejected (q : Agent Empty) :
    ¬ capture.Realizes (extendEnv (fun _ => .name 42) payload) q := by
  intro h
  have hm := ((actual_full_output.capture_realizes_iff φ outputCode continuation payload (.refl _)
    full_output_is_deterministic _ _ _).mp h).1 0
  have hn := (EqE.name_iff 42 40).mp hm
  cases hn

theorem output_keeps_waiting_input : continuation = .input 9 (.output 10 (.var none) .nil) := rfl

theorem scoped_backward_output_keeps_local_and_capture :
    ∃ p n q, SourceVisibleInterpretationSPOT.scopedSource.Realizes (fun _ => .name 42) p ∧
      EqE (.name 41) n ∧ Agent.Visible p (.output 0 n) q ∧ Agent.EvalEq q .nil :=
  SourceAtomicOutputSPOT.output_crosses_variable_scope.realizes_backward (fun _ => .name 42) (.name 41)
    SourceVisibleInterpretationSPOT.scoped_target_has_correct_values

theorem scope_exchange_cannot_be_omitted :
    ¬ EqE (extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 41)) (.name 40) none)
      (extendEnv (extendEnv (fun _ : Nat => (.name 42 : Ground)) (.name 40)) (.name 41) none) :=
  SourceVisibleInterpretationSPOT.omitted_scope_exchange_rejected

abbrev echo : Agent (Option Empty) := .output 8 (.var none) .nil
abbrev inputCode : Agent Empty := .input 7 echo
abbrev inputResult : Agent Empty := .output 8 (.name 40) .nil

theorem actual_handle_input : Extended.FreeStep (Extended.frameProcess φ inputCode) (.input 7 (.var 0))
    (Extended.frameProcess φ inputResult) :=
  Extended.frame_visible_input_derivable φ (.var 0) (.of_core (.input 7 (.name 40) echo))

theorem input_result_is_deterministic (q : Agent Empty)
    (h : Agent.Visible inputCode (.input 7 (φ.eval (.var 0))) q) : Agent.EvalEq q inputResult := by
  apply Agent.EvalEq.of_parEq
  apply Agent.visible_input_deterministic h (Agent.Visible.of_core (.input 7 (.name 40) echo))
  intro a b ha hb
  simp [inputCode,Agent.threads,Agent.threadList] at ha hb
  exact ha.trans hb.symm

theorem input_preserves_all_old_environments (env : Fin 1 → Ground) :
    (∃ p, (Extended.frameProcess φ inputCode).Realizes env p) ↔
      ∃ q, (Extended.frameProcess φ inputResult).Realizes env q := actual_handle_input.has_realization_iff env

theorem input_target_has_full_canonical_class :
    (Extended.frameProcess φ inputResult).SameRealizations (Extended.frameProcess φ inputResult) :=
  actual_handle_input.input_sameRealizations_target φ inputCode inputResult (.refl _) input_result_is_deterministic

theorem backward_input_keeps_exact_recipe_value :
    ∃ p q, (Extended.frameProcess φ inputCode).Realizes φ.value p ∧
      (Extended.FreeLabel.input 7 (.var (0 : Fin 1))).RealizedStep φ.value p q ∧ Agent.EvalEq q inputResult :=
  actual_handle_input.realizes_backward φ.value (Extended.frameProcess_realizes φ inputResult)

abbrev competing : Agent Empty := .par (.output 8 (.name 40) .nil) (.output 8 (.name 41) .nil)

theorem first_competing_output : Agent.Visible competing (.output 8 (.name 40)) (.par .nil (.output 8 (.name 41) .nil)) :=
  (Agent.Visible.of_core (.output _ _ _)).parLeft _

theorem second_competing_output : Agent.Visible competing (.output 8 (.name 41)) (.par (.output 8 (.name 40) .nil) .nil) :=
  (Agent.Visible.of_core (.output _ _ _)).parRight _

theorem output_determinism_cannot_drop_payloads :
    ¬ (∀ c m q n r, Agent.Visible competing (.output c m) q → Agent.Visible competing (.output c n) r →
      EqE m n ∧ Agent.EvalEq q r) := by
  intro h
  have he := (h _ _ _ _ _ first_competing_output second_competing_output).1
  have hn := (EqE.name_iff 40 41).mp he
  cases hn

abbrev rawPublic : Named (Fin 1) := .embed (Extended.frameProcess φ outputCode)
abbrev canonical : ScopedState {40} 1 := ⟨φ,outputCode⟩

theorem unrestricted_process_has_body_invariant : Named.HasCanonicalOpening rawPublic φ outputCode :=
  ⟨[],_,Equiv.refl Nat,Equiv.refl Nat,.embed _ _,by simp,.refl _⟩

theorem restricted_process_has_same_body_invariant :
    Named.HasCanonicalOpening (Named.restrictedState {8} canonical) φ outputCode :=
  Named.restrictedState_hasCanonicalOpening canonical

theorem unrestricted_process_exposes_channel : Named.BoundOutput rawPublic 8 (.embed capture) :=
  .embed actual_full_output

theorem restricted_process_cannot_expose_channel (b : Named (Option (Fin 1))) :
    ¬ Named.BoundOutput (Named.restrictedState {8} canonical) 8 b :=
  Named.restricted_private_bound_blocked canonical b 8 (by decide)

/-- The body invariant alone does not preserve the private-channel policy. -/
theorem body_invariant_alone_does_not_supply_policy :
    Named.HasCanonicalOpening rawPublic φ outputCode ∧
    Named.HasCanonicalOpening (Named.restrictedState {8} canonical) φ outputCode ∧
    Named.BoundOutput rawPublic 8 (.embed capture) ∧
    ¬ Named.BoundOutput (Named.restrictedState {8} canonical) 8 (.embed capture) :=
  ⟨unrestricted_process_has_body_invariant,restricted_process_has_same_body_invariant,
    unrestricted_process_exposes_channel,restricted_process_cannot_expose_channel _⟩

theorem output_all_channels_deterministic (c : Nat) (m : Ground) (q : Agent Empty)
    (n : Ground) (r : Agent Empty)
    (hq : Agent.Visible outputCode (.output c m) q) (hr : Agent.Visible outputCode (.output c n) r) :
    EqE m n ∧ Agent.EvalEq q r := by
  obtain ⟨body,hb⟩ := hq.output_prefix
  simp [outputCode,Agent.threads,Agent.threadList] at hb
  obtain ⟨rfl,_,_⟩ := hb
  obtain ⟨hm,hq'⟩ := full_output_is_deterministic m q hq
  obtain ⟨hn,hr'⟩ := full_output_is_deterministic n r hr
  exact ⟨hm.trans hn.symm,hq'.trans hr'.symm⟩

theorem actual_named_output_retains_full_invariant :
    ∃ (k : Nat ≃ Nat) (m : Ground) (q : Agent Empty),
      Agent.Visible outputCode (.output (k.symm 8) m) q ∧
      Named.HasCanonicalOpening ((Named.embed capture).rename Extended.outputHandle) (φ.extend m) q :=
  unrestricted_process_has_body_invariant.boundOutput unrestricted_process_exposes_channel output_all_channels_deterministic

theorem input_all_channels_deterministic (c : Nat) (m : Ground) (p q : Agent Empty)
    (hp : Agent.Visible inputCode (.input c m) p) (hq : Agent.Visible inputCode (.input c m) q) : Agent.EvalEq p q := by
  apply Agent.EvalEq.of_parEq
  apply Agent.visible_input_deterministic hp hq
  intro a b ha hb
  simp [inputCode,Agent.threads,Agent.threadList] at ha hb
  exact ha.2.trans hb.2.symm

theorem actual_named_input_retains_full_invariant :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty),
      Agent.Visible inputCode (.input (k.symm 7) (φ.eval ((Term.var (0 : Fin 1)).mapNames e.symm))) q ∧
      Named.HasCanonicalOpening (.embed (Extended.frameProcess φ inputResult)) φ q := by
  have ha : Named.HasCanonicalOpening (.embed (Extended.frameProcess φ inputCode)) φ inputCode :=
    ⟨[],_,Equiv.refl Nat,Equiv.refl Nat,.embed _ _,by simp,.refl _⟩
  exact ha.input (Named.FreeStep.embed actual_handle_input) input_all_channels_deterministic

abbrev ens := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right
abbrev ch := Channels.canonical

theorem all_election_inputs_have_unique_full_targets (swap : Bool) (extra : Nat) (phase : Process.Phase)
    (c : Nat) (m : Ground) (p q : Agent Empty)
    (hp : Agent.Visible (residual ens swap left right extra ch phase) (.input c m) p)
    (hq : Agent.Visible (residual ens swap left right extra ch phase) (.input c m) q) : Agent.EvalEq p q :=
  residual_visible_input_deterministic ens swap left right extra ch Channels.canonical_fresh phase c m p q hp hq

theorem all_election_outputs_keep_full_values (swap : Bool) (extra : Nat) (phase : Process.Phase)
    (c : Nat) (m : Ground) (p : Agent Empty) (n : Ground) (q : Agent Empty)
    (hp : Agent.Visible (residual ens swap left right extra ch phase) (.output c m) p)
    (hq : Agent.Visible (residual ens swap left right extra ch phase) (.output c n) q) : EqE m n ∧ Agent.EvalEq p q :=
  residual_visible_output_deterministic ens swap left right extra ch Channels.canonical_fresh phase c m p n q hp hq

end ExplainableCrypto.Helios.Symbolic.SourceVisibleInvariantSPOT
