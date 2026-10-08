import ExplainableCrypto.Helios.Symbolic.SourcePairedVisibleOpenings

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent

/-- Fixed-channel, fixed-full-message input determinism survives coherent
name permutations. No public-policy premise is hidden in this transport. -/
theorem input_determinism_mapNames (p : Agent Empty)
    (hd : ∀ c m q r, Visible p (.input c m) q → Visible p (.input c m) r → EvalEq q r)
    (e k : Nat ≃ Nat) :
    ∀ c m q r, Visible (p.mapNames e k) (.input c m) q →
      Visible (p.mapNames e k) (.input c m) r → EvalEq q r := by
  intro c m q r hq hr
  have hq' : Visible p (.input (k.symm c) (m.mapNames e.symm)) (q.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,PayloadEvent.mapNames] using hq.mapNames e.symm k.symm
  have hr' : Visible p (.input (k.symm c) (m.mapNames e.symm)) (r.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,PayloadEvent.mapNames] using hr.mapNames e.symm k.symm
  have he := (hd _ _ _ _ hq' hr').mapNames e k
  simpa only [show (q.mapNames e.symm k.symm).mapNames e k = q from Agent.mapNames_inverse q e.symm k.symm,
    show (r.mapNames e.symm k.symm).mapNames e k = r from Agent.mapNames_inverse r e.symm k.symm] using he

/-- Full output values and continuations, not only channels, must agree in a
deterministic output. The property is invariant under coherent permutations. -/
theorem output_determinism_mapNames (p : Agent Empty)
    (hd : ∀ c m q n r, Visible p (.output c m) q → Visible p (.output c n) r → EqE m n ∧ EvalEq q r)
    (e k : Nat ≃ Nat) :
    ∀ c m q n r, Visible (p.mapNames e k) (.output c m) q →
      Visible (p.mapNames e k) (.output c n) r → EqE m n ∧ EvalEq q r := by
  intro c m q n r hq hr
  have hq' : Visible p (.output (k.symm c) (m.mapNames e.symm)) (q.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,PayloadEvent.mapNames] using hq.mapNames e.symm k.symm
  have hr' : Visible p (.output (k.symm c) (n.mapNames e.symm)) (r.mapNames e.symm k.symm) := by
    simpa only [Agent.mapNames_inverse,PayloadEvent.mapNames] using hr.mapNames e.symm k.symm
  obtain ⟨hm,he⟩ := hd _ _ _ _ _ hq' hr'
  constructor
  · simpa only [show (m.mapNames e.symm).mapNames e = m from Term.mapNames_inverse m e.symm,
      show (n.mapNames e.symm).mapNames e = n from Term.mapNames_inverse n e.symm] using hm.mapNames e
  · simpa only [show (q.mapNames e.symm k.symm).mapNames e k = q from Agent.mapNames_inverse q e.symm k.symm,
      show (r.mapNames e.symm k.symm).mapNames e k = r from Agent.mapNames_inverse r e.symm k.symm] using he.mapNames e k

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
