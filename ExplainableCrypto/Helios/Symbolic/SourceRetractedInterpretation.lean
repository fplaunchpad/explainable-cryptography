import ExplainableCrypto.Helios.Symbolic.SourceReadyGuardRetractions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- The whole actual Extended reduction is interpreted first; recovering its
ready guards modulo E then transports the actual Tau and full target. The
source environment moves with the name map. No Named witness is asserted. -/
theorem Reduction.realizes_mapNames_of_guard_retractions {a b : Extended V}
    (h : Reduction a b) (env : V → Ground) {p : Agent Empty}
    (ha : a.Realizes env p) (f g k : Nat → Nat) (hr : p.ReadyGuardsRetract f g) :
    ∃ q : Agent Empty, Agent.Tau (p.mapNames f k) (q.mapNames f k) ∧
      (b.mapNames f k).Realizes (fun v => (env v).mapNames f) (q.mapNames f k) := by
  obtain ⟨q,hq,hb⟩ := h.realizes env ha
  exact ⟨q,hq.mapNames_of_guard_retractions f g k hr,hb.mapNames f k⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
