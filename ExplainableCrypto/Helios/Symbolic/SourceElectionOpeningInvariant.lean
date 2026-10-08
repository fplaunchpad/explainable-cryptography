import ExplainableCrypto.Helios.Symbolic.SourceInternalFrameIdentity

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

namespace Named
variable {V : Type} {restricted : Finset Nat} {before after : Nat}

theorem rename_id (a : Named V) : a.rename id = a := by
  induction a with
  | embed a => exact congrArg Named.embed a.rename_id
  | par a b ha hb => simp only [Named.rename,ha,hb]
  | newName n a ih => simp only [Named.rename,ih]
  | newVar a ih =>
    rename_i V'
    have he : Option.map (id : V' → V') = id := by funext v; cases v <;> rfl
    simpa only [Named.rename,he] using congrArg Named.newVar ih

theorem HasCanonicalOpening.cast_handles {a : Named (Fin before)}
    {φ : Frame restricted before} {ψ : Frame restricted after} {p : Agent Empty}
    (h : HasCanonicalOpening a φ p) (hh : before = after) (he : HEq φ ψ) :
    HasCanonicalOpening (a.rename (Fin.cast hh)) ψ p := by
  subst after
  cases he
  simpa only [show Fin.cast (Eq.refl before) = (id : Fin before → Fin before) from rfl,rename_id] using h

theorem Reduction.cast_handles {a b : Named (Fin before)} (h : Reduction a b) (hh : before = after) :
    Reduction (a.rename (Fin.cast hh)) (b.rename (Fin.cast hh)) := by
  subst after
  simpa only [show Fin.cast (Eq.refl before) = (id : Fin before → Fin before) from rfl,rename_id] using h

end Named
variable {n : Nat}

/-- Arbitrary source internal actions preserve the full canonical-opening
invariant at the actual next phase. This consumes the invariant itself, so
it can be invoked repeatedly on raw targets. Handle transport is explicit. -/
theorem source_opening_internal_next (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra)
    {a b : Named (Fin phase.handles)}
    (ha : Named.HasCanonicalOpening a (sourceView ns swap left right phase)
      (residual ns swap left right extra ch phase)) (h : Named.Reduction a b) :
    ∃ (next : Process.Phase) (hh : phase.handles = next.handles),
      Process.Step ns swap left right extra phase .tau next ∧
      Named.HasCanonicalOpening (b.rename (Fin.cast hh)) (sourceView ns swap left right next)
        (residual ns swap left right extra ch next) := by
  obtain ⟨q,hq⟩ := ha.tau h
  obtain ⟨next,hs,_⟩ := residual_tau_complete ns swap left right extra ch hc phase hr hq
  have ht := ha.internal h (fun r hr' => Agent.EvalEq.of_parEq
    (residual_tau_deterministic ns swap left right extra ch hc phase hr hr'
      (residual_tau_step ns swap left right extra ch hs)))
  exact ⟨next,hs.tau_handles,hs,ht.cast_handles hs.tau_handles hs.tau_sourceView⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
