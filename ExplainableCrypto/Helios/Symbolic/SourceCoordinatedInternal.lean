import ExplainableCrypto.Helios.Symbolic.SourceCoordinatedPhases

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Named
variable {restricted hidden : Finset Nat} {before after : Nat} {e k : Nat ≃ Nat}

theorem JointOpening.cast_mapped_state {a : Named (Fin before)}
    {s : ScopedState restricted before} {t : ScopedState restricted after}
    (h : JointOpening a (mappedState hidden s e k)) (hh : before = after) (he : HEq s t) :
    JointOpening (a.rename (Fin.cast hh)) (mappedState hidden t e k) := by
  subst after
  cases he
  simpa only [show Fin.cast (Eq.refl before) = (id : Fin before → Fin before) from rfl,rename_id] using h
end Named
variable {n : Nat}

theorem source_coordinated_internal_next (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (hr : phase.inRange extra)
    {a b : Named (Fin phase.handles)}
    (ha : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k))
    (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (hh : phase.handles = next.handles),
      Process.Step ns swap left right extra phase .tau next ∧
      Named.JointOpening (b.rename (Fin.cast hh))
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch next) e k) := by
  obtain ⟨q,hq⟩ := ha.tau h
  have hqi : Agent.Tau (residual ns swap left right extra ch phase) (q.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,sourceState] using hq.mapNames e.symm k.symm
  obtain ⟨next,hs,_⟩ := residual_tau_complete ns swap left right extra ch hc phase hr hqi
  have hdet := Agent.tau_target_mapNames (residual ns swap left right extra ch phase)
    (residual ns swap left right extra ch next)
    (fun r hr' => Agent.EvalEq.of_parEq (residual_tau_deterministic ns swap left right extra ch hc phase hr hr'
      (residual_tau_step ns swap left right extra ch hs))) e k
  have ht := ha.internal h hdet
  exact ⟨next,hs.tau_handles,hs,ht.cast_mapped_state hs.tau_handles (hs.tau_target_state ch)⟩

variable {handles : Nat} {ns : Names n} {swap : Bool}
  {left right : CandidateSubstitution n Empty} {extra : Nat} {ch : Channels}
  {e k : Nat ≃ Nat} {phase : Process.Phase}

theorem CoordinatedPhaseOpening.internal {a b : Named (Fin handles)}
    (ha : CoordinatedPhaseOpening ns swap left right extra ch e k phase a) (hc : ch.Fresh)
    (hr : phase.inRange extra) (h : Named.Reduction a b) :
    ∃ next, Process.Step ns swap left right extra phase .tau next ∧
      CoordinatedPhaseOpening ns swap left right extra ch e k next b := by
  obtain ⟨hh,ha⟩ := ha
  obtain ⟨next,hj,hs,hb⟩ := source_coordinated_internal_next ns swap left right extra ch hc e k phase hr ha (h.cast_handles hh)
  refine ⟨next,hs,hh.trans hj,?_⟩
  have he : Fin.cast hj ∘ Fin.cast hh = Fin.cast (hh.trans hj) := by funext i; rfl
  simpa only [Named.rename_comp,he] using hb

/-- Subsequent finite raw internal traces retain the current common coordinates,
including after an input has freshened the original private-name policy. -/
theorem CoordinatedPhaseOpening.internal_trace {a b : Named (Fin handles)}
    (ha : CoordinatedPhaseOpening ns swap left right extra ch e k phase a) (hc : ch.Fresh)
    (hr : Process.Reachable ns swap left right extra phase)
    (h : Relation.ReflTransGen (@Named.Reduction (Fin handles)) a b) :
    ∃ next, Process.Reachable ns swap left right extra next ∧
      Relation.ReflTransGen (fun p q => Process.Step ns swap left right extra p .tau q) phase next ∧
      CoordinatedPhaseOpening ns swap left right extra ch e k next b := by
  induction h with
  | refl => exact ⟨phase,hr,.refl,ha⟩
  | tail h hstep ih =>
    obtain ⟨current,hr',ht,ha'⟩ := ih
    obtain ⟨next,hs,hb⟩ := ha'.internal hc hr'.wellFormed.inRange hstep
    exact ⟨next,hr'.tail ⟨.tau,hs⟩,ht.tail hs,hb⟩

theorem CoordinatedPhaseOpening.bound_channel_public {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    (ha : CoordinatedPhaseOpening ns swap left right extra ch e k phase a) {c : Nat}
    (h : Named.BoundOutput a c b) : c ∉ ch.privateChannels.image k := by
  have hc := h.channel_mem
  rw [ha.channels] at hc
  exact ((Named.channel_mem_restrictedState _ _ c).mp hc).2

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
