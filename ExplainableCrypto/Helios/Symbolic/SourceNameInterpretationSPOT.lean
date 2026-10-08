import ExplainableCrypto.Helios.Symbolic.SourceFreshInterpretation
import ExplainableCrypto.Helios.Symbolic.SourceVisibleInterpretationSPOT
import ExplainableCrypto.Helios.Symbolic.SourceFreshNamesSPOT
import ExplainableCrypto.Helios.Symbolic.SourceNamedPrenex

namespace ExplainableCrypto.Helios.Symbolic.SourceNameInterpretationSPOT
open Historical General Source Extended

abbrev e : Nat ≃ Nat := Equiv.swap 40 50
abbrev binding : Extended (Fin 1) := .active 0 (.name 40)

theorem alpha_binding_representative :
    Named.Structural (.newName (.base 40) (.embed binding))
      (.newName (.base 50) (.embed (binding.mapNames e id))) :=
  .alphaBase _ _ _ (by decide)

theorem moved_binding_has_moved_environment :
    (binding.mapNames e id).Realizes (fun _ => .name 50) .nil := by
  have h : binding.Realizes (fun _ => .name 40) .nil := ⟨.refl _,.refl _⟩
  simpa only [Term.mapNames,e,Equiv.swap_apply_left,Agent.mapNames] using h.mapNames e id

theorem stale_alpha_environment_rejected :
    ¬ (binding.mapNames e id).Realizes (fun _ => .name 40) .nil := by
  intro h
  have he : EqE (.name 40 : Ground) (.name 50) := by
    simpa only [binding,Extended.mapNames,Realizes,Term.mapNames,Term.subst,e,Equiv.swap_apply_left] using h.1
  exact (by decide : (40 : Nat) ≠ 50) ((EqE.name_iff 40 50).mp he)

/-- A collapse admits an inconsistent old binding. Forward transport does not
justify reflection without a bijection. -/
theorem name_collapse_cannot_reflect :
    (binding.mapNames (fun _ => 0) id).Realizes (fun _ => .name 0) .nil ∧
    ¬ binding.Realizes (fun _ => .name 41) .nil := by
  refine ⟨⟨.refl _,.refl _⟩,?_⟩
  intro h
  exact (by decide : (41 : Nat) ≠ 40) ((EqE.name_iff 41 40).mp h.1)

theorem channel_collapse_cannot_reflect :
    Agent.EquivE ((.output 8 (.name 40) .nil : Agent Empty).mapNames id (fun _ => 0))
      ((.output 9 (.name 40) .nil : Agent Empty).mapNames id (fun _ => 0)) ∧
    ¬ Agent.EquivE (.output 8 (.name 40) .nil : Agent Empty) (.output 9 (.name 40) .nil) := by
  exact ⟨.output 0 (.refl _) .nil,by intro h; cases h⟩

/-- The input label's payload and the received continuation move together. -/
theorem mapped_input_has_exact_message :
    (FreeLabel.input 8 (.name 40 : Ground)).mapNames e (Equiv.swap 8 18) |>.RealizedStep Empty.elim
      (.input 18 SourceVisibleInterpretationSPOT.echo) (.output 9 (.name 50) .nil) := by
  have h : (FreeLabel.input 8 (.name 40 : Ground)).RealizedStep Empty.elim
      (.input 8 SourceVisibleInterpretationSPOT.echo) (.output 9 (.name 40) .nil) :=
    Agent.Visible.of_core (.input _ _ _)
  have he : (fun v : Empty => (Empty.elim v : Ground).mapNames e) = Empty.elim := by funext v; exact v.elim
  have hk : Equiv.swap 8 18 (9 : Nat) = 9 := by decide
  simpa [he,hk,Agent.mapNames,SourceVisibleInterpretationSPOT.echo,Term.mapNames,e] using
    h.mapNames e (Equiv.swap 8 18)

theorem capture_environment_names_commute :
    (capture (.name 40 : Term Nat) (.output 9 (.var 7) .nil)).mapNames e id |>.Realizes
      (extendEnv (fun _ => .name 50) (.name 50)) (.output 9 (.name 50) .nil) := by
  have h := capture_realizes (.name 40 : Term Nat) (.output 9 (.var 7) .nil)
    (fun _ => (.name 40 : Ground)) (EqE.refl (.name 40))
  simpa only [Term.mapNames,e,Equiv.swap_apply_left,Agent.mapNames,Agent.subst,Term.subst,id] using
    h.capture_mapNames e id

/-- Old key and complete four-field proof move under one base permutation. -/
theorem complete_frame_name_transport :
    ((SourceVisibleInterpretationSPOT.oldFrame.extend SourceVisibleInterpretationSPOT.proofPayload).mapNames e).value 0 =
      .unary .pk (.name 50) ∧
    ((SourceVisibleInterpretationSPOT.oldFrame.extend SourceVisibleInterpretationSPOT.proofPayload).mapNames e).value 1 =
      .spk (.unary .pk (.name 50)) (.name 41) (.const .zero)
        (.ternary .penc (.unary .pk (.name 50)) (.name 41) (.const .one)) := by
  decide

/-- Reflection recovers the entire original captured interpretation. -/
theorem inverse_capture_recovers_environment (a : Extended (Option Nat)) (env : Nat → Ground)
    (m : Ground) (p : Agent Empty)
    (h : (a.mapNames e id).Realizes (extendEnv (fun v => (env v).mapNames e) (m.mapNames e))
      (p.mapNames e id)) : a.Realizes (extendEnv env m) p :=
  (capture_realizes_mapNames_iff a env m p e (Equiv.refl Nat)).mp h

/-- Both actual election worlds can freshen while retaining their complete
interpreted frame/body pairs and all two-world public observations. -/
theorem fresh_actual_worlds_keep_interpretation (phase : Process.Phase)
    (h : Process.Reachable SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 phase)
    (r : Recipe phase.handles) :
    ∃ e k : Nat ≃ Nat,
      r.Public (SharedTallySPOT.names.restricted.image e) ∧ k 4 = 4 ∧
      ((sourceView SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right phase).mapNames e).StaticEq
        ((sourceView SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right phase).mapNames e) ∧
      (frameProcess
        ((sourceView SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right phase).mapNames e)
        ((residual SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical phase).mapNames e k)).Realizes
        ((sourceView SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right phase).mapNames e).value
        ((residual SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical phase).mapNames e k) := by
  obtain ⟨e,k,_,_,hr,hc,he,hp,_⟩ := Named.exists_common_fresh_interpreted_input
    (sourceState SharedTallySPOT.names false SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical phase)
    (sourceState SharedTallySPOT.names true SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical phase)
    (hidden := Channels.canonical.privateChannels) 4 r (by decide)
    (reachable_source_view_staticEq NumericReflectionSPOT.fixture_names_fresh h)
  exact ⟨e,k,hr,hc,he,hp⟩

abbrev publicSender : Named Empty := .embed (.plain (.output 8 (.name 40) .nil))
abbrev privateReceiver : Named Empty := .newName (.channel 8) (.embed (.plain (.input 8 .nil)))

/-- Freshening the receiver channel before extrusion retains the sender's
public channel. The two equal numeric channel literals originally have different scopes. -/
theorem prenex_extrusion_avoids_public_sender :
    Named.Structural (.par publicSender privateReceiver)
      (.newName (.channel 18) (.embed (.par (.plain (.output 8 (.name 40) .nil))
        (.plain (.input 18 .nil))))) := by
  have ha : Named.Structural privateReceiver
      (.newName (.channel 18) (.embed (.plain (.input 18 .nil)))) := by
    simpa only [Named.mapNames,Extended.mapNames,Agent.mapNames,Equiv.swap_apply_left]
      using Named.Structural.alphaChannel (.embed (.plain (.input 8 .nil) : Extended Empty)) 8 18 (by decide)
  exact (Named.Structural.parRight publicSender ha).trans
    ((Named.Structural.namePar publicSender (.channel 18) _ (by decide)).trans
      (.newName (.channel 18) (Named.Structural.embedPar _ _).symm))

theorem unfresh_channel_extrusion_rejected :
    ¬ Named.Structural (.par publicSender privateReceiver)
      (.newName (.channel 8) (.par publicSender (.embed (.plain (.input 8 .nil))))) := by
  intro h
  have he := h.channels
  have hm : 8 ∈ (Named.par publicSender privateReceiver).channels := by decide
  rw [he] at hm
  exact (by decide : 8 ∉ (Named.newName (.channel 8)
    (.par publicSender (.embed (.plain (.input 8 .nil))))).channels) hm

theorem mixed_context_has_distinct_fresh_prenex :
    ∃ (ns : List SourceName) (b : Extended (Fin 1)),
      Named.Structural
        (.newVar (.par (.newName (.base 40) (.embed (.active none (.name 40))))
          (.newName (.channel 8) (.embed (.plain (.input 8 .nil))))))
        (Named.restrictNames ns (.embed b)) ∧
      ns.Nodup ∧ ∀ n ∈ ns, n ∉ ({.base 40,.channel 8} : Finset SourceName) :=
  Named.exists_distinct_fresh_prenex _ _

end ExplainableCrypto.Helios.Symbolic.SourceNameInterpretationSPOT
