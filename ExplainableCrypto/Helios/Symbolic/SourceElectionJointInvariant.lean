import ExplainableCrypto.Helios.Symbolic.SourceJointOpeningInternal
import ExplainableCrypto.Helios.Symbolic.SourceOpeningInternalTraces

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Named
variable {restricted hidden : Finset Nat} {before after : Nat}

theorem JointOpening.cast_state {a : Named (Fin before)}
    {s : ScopedState restricted before} {t : ScopedState restricted after}
    (h : JointOpening a (restrictedState hidden s)) (hh : before = after) (he : HEq s t) :
    JointOpening (a.rename (Fin.cast hh)) (restrictedState hidden t) := by
  subst after
  cases he
  simpa only [show Fin.cast (Eq.refl before) = (id : Fin before → Fin before) from rfl,rename_id] using h
end Named

variable {n : Nat}

/-- Every raw internal action has an actual next election phase, retaining the
joint relation with the full restricted canonical state and exact handle domain.
Election residual determinism discharges the generic closure premise. -/
theorem source_joint_internal_next (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {a b : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.restrictedState ch.privateChannels
      (sourceState ns swap left right extra ch phase))) (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (hh : phase.handles = next.handles),
      Process.Step ns swap left right extra phase .tau next ∧
      Named.JointOpening (b.rename (Fin.cast hh)) (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch next)) := by
  obtain ⟨q,hq⟩ := ha.tau h
  obtain ⟨next,hs,_⟩ := residual_tau_complete ns swap left right extra ch hc phase hr hq
  have ht := ha.internal h (fun r hr' => Agent.EvalEq.of_parEq
    (residual_tau_deterministic ns swap left right extra ch hc phase hr hr'
      (residual_tau_step ns swap left right extra ch hs)))
  exact ⟨next,hs.tau_handles,hs,ht.cast_state hs.tau_handles (hs.tau_target_state ch)⟩

/-- The joint full-state relation at an election phase, with exact public handle
domain transport. Both original restriction policies remain in the relation. -/
def PhaseJointOpening {n handles : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (a : Named (Fin handles)) : Prop :=
  ∃ hh : handles = phase.handles,
    Named.JointOpening (a.rename (Fin.cast hh)) (Named.restrictedState ch.privateChannels
      (sourceState ns swap left right extra ch phase))

variable {handles : Nat} {ns : Names n} {swap : Bool}
  {left right : CandidateSubstitution n Empty} {extra : Nat} {ch : Channels}
  {phase : Process.Phase}

theorem PhaseJointOpening.canonical :
    PhaseJointOpening ns swap left right extra ch phase
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)) := by
  refine ⟨rfl,?_⟩
  simpa only [show Fin.cast (Eq.refl phase.handles) = id from rfl,Named.rename_id] using
    Named.restrictedState_jointOpening (hidden := ch.privateChannels)
      (sourceState ns swap left right extra ch phase)

theorem PhaseJointOpening.structural {a b : Named (Fin handles)}
    (ha : PhaseJointOpening ns swap left right extra ch phase a) (h : Named.Structural a b) :
    PhaseJointOpening ns swap left right extra ch phase b := by
  obtain ⟨hh,ha⟩ := ha
  exact ⟨hh,ha.structural_left (h.rename (Fin.cast hh) (Fin.cast_injective hh))⟩

theorem PhaseJointOpening.bodyInvariant {a : Named (Fin handles)}
    (ha : PhaseJointOpening ns swap left right extra ch phase a) :
    PhaseOpening ns swap left right extra ch phase a := by
  obtain ⟨hh,ha⟩ := ha
  exact ⟨hh,ha.hasCanonicalOpening (sourceState ns swap left right extra ch phase)⟩

theorem PhaseJointOpening.internal {a b : Named (Fin handles)}
    (ha : PhaseJointOpening ns swap left right extra ch phase a) (hc : ch.Fresh)
    (hr : phase.inRange extra) (h : Named.Reduction a b) :
    ∃ next, Process.Step ns swap left right extra phase .tau next ∧
      PhaseJointOpening ns swap left right extra ch next b := by
  obtain ⟨hh,ha⟩ := ha
  obtain ⟨next,hj,hs,hb⟩ := source_joint_internal_next ns swap left right extra ch hc phase hr ha
    (h.cast_handles hh)
  refine ⟨next,hs,hh.trans hj,?_⟩
  have he : Fin.cast hj ∘ Fin.cast hh = Fin.cast (hh.trans hj) := by funext i; rfl
  simpa only [Named.rename_comp,he] using hb

/-- Finite raw internal traces preserve the full joint relation, reached phase
and matching internal stage trace. No raw target needs a Structural presentation. -/
theorem PhaseJointOpening.internal_trace {a b : Named (Fin handles)}
    (ha : PhaseJointOpening ns swap left right extra ch phase a) (hc : ch.Fresh)
    (hr : Process.Reachable ns swap left right extra phase)
    (h : Relation.ReflTransGen (@Named.Reduction (Fin handles)) a b) :
    ∃ next, Process.Reachable ns swap left right extra next ∧
      Relation.ReflTransGen (fun p q => Process.Step ns swap left right extra p .tau q) phase next ∧
      PhaseJointOpening ns swap left right extra ch next b := by
  induction h with
  | refl => exact ⟨phase,hr,.refl,ha⟩
  | tail h hstep ih =>
    obtain ⟨current,hr',ht,ha'⟩ := ih
    obtain ⟨next,hs,hb⟩ := ha'.internal hc hr'.wellFormed.inRange hstep
    exact ⟨next,hr'.tail ⟨.tau,hs⟩,ht.tail hs,hb⟩

theorem PhaseJointOpening.channels {a : Named (Fin handles)}
    (ha : PhaseJointOpening ns swap left right extra ch phase a) :
    a.channels = (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)).channels := by
  obtain ⟨hh,ha⟩ := ha
  simpa only [Named.channels_rename] using ha.channels

theorem PhaseJointOpening.free_channel_public {a b : Named (Fin handles)}
    (ha : PhaseJointOpening ns swap left right extra ch phase a)
    {l : Extended.FreeLabel (Fin handles)} (h : Named.FreeStep a l b) : l.channel ∉ ch.privateChannels := by
  have hc := h.channel_mem
  rw [ha.channels] at hc
  exact ((Named.channel_mem_restrictedState ch.privateChannels _ l.channel).mp hc).2

theorem PhaseJointOpening.bound_channel_public {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    (ha : PhaseJointOpening ns swap left right extra ch phase a)
    {c : Nat} (h : Named.BoundOutput a c b) : c ∉ ch.privateChannels := by
  have hc := h.channel_mem
  rw [ha.channels] at hc
  exact ((Named.channel_mem_restrictedState ch.privateChannels _ c).mp hc).2

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
