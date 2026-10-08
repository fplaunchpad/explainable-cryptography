import ExplainableCrypto.Helios.Symbolic.SourceInterpretationNames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

theorem FreeLabel.RealizedStep.mapNames {env : V → Ground} {l : FreeLabel V}
    {p q : Agent Empty} (h : l.RealizedStep env p q) (f g : Nat → Nat) :
    (l.mapNames f g).RealizedStep (fun v => (env v).mapNames f) (p.mapNames f g) (q.mapNames f g) := by
  cases l with
  | input c m =>
    simpa only [FreeLabel.mapNames,FreeLabel.RealizedStep,Agent.PayloadEvent.mapNames,Term.mapNames_subst] using
      Agent.Visible.mapNames h f g
  | output c x =>
    obtain ⟨m,hm,hq⟩ := h
    exact ⟨m.mapNames f,hm.mapNames f,hq.mapNames f g⟩

theorem FreeLabel.realizedStep_mapNames_iff (env : V → Ground) (l : FreeLabel V)
    (p q : Agent Empty) (e k : Nat ≃ Nat) :
    (l.mapNames e k).RealizedStep (fun v => (env v).mapNames e) (p.mapNames e k) (q.mapNames e k) ↔
      l.RealizedStep env p q := by
  constructor
  · intro h
    simpa only [FreeLabel.mapNames_inverse,Term.mapNames_inverse,Agent.mapNames_inverse] using
      h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

/-- A realized raw output target moves under the same map as its actual new
message; all old environment values move consistently and keep their indices. -/
theorem Realizes.capture_mapNames {a : Extended (Option V)} {env : V → Ground}
    {m : Ground} {p : Agent Empty} (h : a.Realizes (extendEnv env m) p) (f g : Nat → Nat) :
    (a.mapNames f g).Realizes (extendEnv (fun v => (env v).mapNames f) (m.mapNames f)) (p.mapNames f g) := by
  simpa only [extendEnv_mapNames] using h.mapNames f g

theorem capture_realizes_mapNames_iff (a : Extended (Option V)) (env : V → Ground)
    (m : Ground) (p : Agent Empty) (e k : Nat ≃ Nat) :
    (a.mapNames e k).Realizes (extendEnv (fun v => (env v).mapNames e) (m.mapNames e)) (p.mapNames e k) ↔
      a.Realizes (extendEnv env m) p := by
  simpa only [extendEnv_mapNames] using realizes_mapNames_iff a (extendEnv env m) p e k

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
