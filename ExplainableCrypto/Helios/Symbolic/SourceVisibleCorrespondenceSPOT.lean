import ExplainableCrypto.Helios.Symbolic.SourceVisibleCorrespondence
import ExplainableCrypto.Helios.Symbolic.SourceScopedSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceVisibleCorrespondenceSPOT
open Historical General Source
abbrev ch := Channels.canonical
abbrev ns := SharedTallySPOT.names
abbrev left := SharedTallySPOT.left
abbrev right := SharedTallySPOT.right

/-- The first publication exports its actual ballot while retaining the key. -/
theorem first_publication_keeps_key (swap : Bool) :
    ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right 1 ch .firstReceived)
      (.output 0) (sourceState ns swap left right 1 ch .firstPublished) ∧
    (sourceView ns swap left right .firstPublished).value (0 : Fin 2) = publicKey ns ∧
    (sourceView ns swap left right .firstPublished).value (1 : Fin 2) = ballot ns 0 (choice swap left right 0).value := by
  refine ⟨?_,rfl,rfl⟩
  apply (scoped_output_iff _ _ _).mpr
  refine ⟨by decide,ballot ns 0 (choice swap left right 0).value,?_,?_⟩
  · exact (eq_of_heq (Publication.capture (Publication.first (ns := ns) (swap := swap)
      (left := left) (right := right) (extra := 1)))).symm
  · exact Agent.Visible.of_core (.parRight _ (.parLeft _ (.output _ _ _)))

/-- With no extra voters, the second output captures all three initial handles
and leaves the private tally send as the next action. -/
theorem zero_extra_second_publication (swap : Bool) :
    ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right 0 ch .secondReceived)
      (.output 0) (sourceState ns swap left right 0 ch (.sendTally [])) ∧
    (sourceView ns swap left right (.sendTally [])).value (2 : Fin 3) = ballot ns 1 (choice swap left right 1).value := by
  refine ⟨?_,rfl⟩
  apply (scoped_output_iff _ _ _).mpr
  refine ⟨by decide,ballot ns 1 (choice swap left right 1).value,?_,?_⟩
  · exact (eq_of_heq (Publication.capture (Publication.second (ns := ns) (swap := swap)
      (left := left) (right := right) (extra := 0)))).symm
  · exact Agent.Visible.of_core (.parLeft _ (.output _ _ _))

/-- The third public channel cannot be skipped in favor of the fourth voter. -/
theorem later_voter_input_blocked (swap : Bool) (q : ScopedState ns.restricted 3) :
    ¬ ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right 1 ch (.input []))
      (.input 5 (.var (1 : Fin 3))) q := by
  intro h
  obtain ⟨_,rs,he,hc,_⟩ := (source_scoped_input_iff ns swap left right 1 ch Channels.canonical_fresh
    (.input []) (by change 0 < 1; decide) 5 (.var (1 : Fin 3)) q).mp h
  cases he
  contradiction

/-- A pending check cannot receive another input before its guard is decided. -/
theorem pending_check_input_blocked (swap : Bool) (q : ScopedState ns.restricted 3) :
    ¬ ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right 1 ch (.check [] (.var (1 : Fin 3))))
      (.input 4 (.var (1 : Fin 3))) q := by
  intro h
  obtain ⟨_,rs,he,_⟩ := (source_scoped_input_iff ns swap left right 1 ch Channels.canonical_fresh
    (.check [] (.var (1 : Fin 3))) (by change 0 < 1; decide) 4 (.var (1 : Fin 3)) q).mp h
  cases he

/-- Replacing the actual ballot output by bottom is impossible even if the
continuation is allowed arbitrary parallel rearrangements. -/
theorem ballot_redaction_blocked (swap : Bool) (q : Agent Empty) :
    ¬ Agent.Visible (residual ns swap left right 1 ch .firstReceived) (.output 0 (.const .bottom)) q := by
  intro h
  obtain ⟨handle,next,hpub,_⟩ := (residual_public_output_iff ns swap left right 1 ch .firstReceived
    (by trivial) 0 (.const .bottom) q (by decide)).mp h
  cases hpub

/-- A forged old handle is rejected even when the newly emitted ballot and
continuation are correct. Capturing an output must not overwrite the key. -/
theorem overwritten_key_blocked (swap : Bool) :
    ¬ ScopedStep ch.privateChannels ns.restricted (sourceState ns swap left right 1 ch .firstReceived)
      (.output 0) ⟨⟨fun i : Fin 2 => if i=0 then .const .bottom else ballot ns 0 (choice swap left right 0).value⟩,
        residual ns swap left right 1 ch .firstPublished⟩ := by
  intro h
  obtain ⟨handle,m,next,hpub,_,he,_⟩ := (source_scoped_output_iff ns swap left right 1 ch Channels.canonical_fresh
    .firstReceived (by trivial) 0 _).mp h
  cases hpub
  have hh := congrArg (fun f : Frame ns.restricted 2 => f.value 0) he
  change (Term.const .bottom : Ground) = .unary .pk (.name ns.secretKey) at hh
  cases hh

/-- The generic input rule retains an unrelated waiting thread. -/
theorem input_retains_waiting_thread (m : Ground) :
    Agent.Visible (.par (.input 4 SourceScopedSPOT.echo) (.input 1 .nil)) (.input 4 m)
      (.par (.output 0 m .nil) (.input 1 .nil)) :=
  Agent.Visible.of_core (.parLeft _ (.input _ _ _))

/-- Removing that thread is detectable by the parallel normal form. -/
theorem dropped_waiting_thread_blocked (m : Ground) :
    ¬ Agent.Visible (.par (.input 4 SourceScopedSPOT.echo) (.input 1 .nil)) (.input 4 m) (.output 0 m .nil) := by
  intro h
  have he := Agent.visible_input_deterministic h (input_retains_waiting_thread m) (by
    intro a b ha hb
    simp [Agent.threads,Agent.threadList] at ha hb
    exact ha.trans hb.symm)
  have hh := congrArg Multiset.card he.threads_eq
  simp [Agent.threads,Agent.threadList] at hh

/-- Actual source views have indistinguishable public observations at a reached
state, independently of whether the forthcoming input will be accepted. -/
theorem initial_source_views_staticEq :
    Frame.StaticEq (sourceView ns false left right .start) (sourceView ns true left right .start) :=
  reachable_source_view_staticEq NumericReflectionSPOT.fixture_names_fresh
    (show Process.Reachable ns false left right 1 .start from .refl)
end ExplainableCrypto.Helios.Symbolic.SourceVisibleCorrespondenceSPOT
