import ExplainableCrypto.Helios.Symbolic.SourceElectionVisibleDeterminism

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- Election residual determinism discharges the full input-closure premise.
The pulled-back channel and complete recipe remain explicit; public-policy
alignment is not asserted by this semantic invariant theorem. -/
theorem source_opening_input_preserved (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) {a b : Named (Fin phase.handles)}
    (ha : Named.HasCanonicalOpening a (sourceView ns swap left right phase)
      (residual ns swap left right extra ch phase)) {c : Nat} {r : Recipe phase.handles}
    (h : Named.FreeStep a (.input c r) b) :
    ∃ (e k : Nat ≃ Nat) (q : Agent Empty),
      Agent.Visible (residual ns swap left right extra ch phase)
        (.input (k.symm c) ((sourceView ns swap left right phase).eval (r.mapNames e.symm))) q ∧
      Named.HasCanonicalOpening b (sourceView ns swap left right phase) q :=
  ha.input h (residual_visible_input_deterministic ns swap left right extra ch hc phase)

/-- Election output closure keeps the complete emitted value, new handle and
full continuation. Canonical public-label/next-phase alignment remains separate. -/
theorem source_opening_output_preserved (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) {a : Named (Fin phase.handles)} {b : Named (Option (Fin phase.handles))}
    (ha : Named.HasCanonicalOpening a (sourceView ns swap left right phase)
      (residual ns swap left right extra ch phase)) {c : Nat} (h : Named.BoundOutput a c b) :
    ∃ (k : Nat ≃ Nat) (m : Ground) (q : Agent Empty),
      Agent.Visible (residual ns swap left right extra ch phase) (.output (k.symm c) m) q ∧
      Named.HasCanonicalOpening (b.rename Extended.outputHandle) ((sourceView ns swap left right phase).extend m) q :=
  ha.boundOutput h (residual_visible_output_deterministic ns swap left right extra ch hc phase)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
