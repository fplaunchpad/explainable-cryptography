import ExplainableCrypto.Helios.Symbolic.SourceCanonicalOpeningInternal

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
open Source
variable {n : Nat}

/-- Internal stage transitions preserve the public handle domain exactly. -/
theorem Process.Step.tau_handles {ns : Names n} {swap : Bool}
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p q : Process.Phase}
    (h : Process.Step ns swap left right extra p .tau q) : p.handles = q.handles := by
  cases h with
  | @accept rs r _ =>
    by_cases hroom : (rs++[r]).length < extra
    · have he : Process.afterAccepted extra (rs++[r]) = .input (rs++[r]) := if_pos hroom
      rw [he]; rfl
    · have he : Process.afterAccepted extra (rs++[r]) = .sendTally (rs++[r]) := if_neg hroom
      rw [he]; rfl
  | _ => rfl

/-- Internal transitions retain the full actual source frame, including check
acceptance/rejection and both private trustee handshakes. -/
theorem Process.Step.tau_sourceView {ns : Names n} {swap : Bool}
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p q : Process.Phase}
    (h : Process.Step ns swap left right extra p .tau q) :
    HEq (sourceView ns swap left right p) (sourceView ns swap left right q) := by
  cases h with
  | @accept rs r _ =>
    by_cases hroom : (rs++[r]).length < extra
    · have he : Process.afterAccepted extra (rs++[r]) = .input (rs++[r]) := if_pos hroom
      rw [he]; rfl
    · have he : Process.afterAccepted extra (rs++[r]) = .sendTally (rs++[r]) := if_neg hroom
      rw [he]; rfl
  | _ => rfl

theorem Process.Step.tau_target_state {ns : Names n} {swap : Bool}
    {left right : CandidateSubstitution n Empty} {extra : Nat} {p q : Process.Phase}
    (h : Process.Step ns swap left right extra p .tau q) (ch : Channels) :
    HEq (⟨sourceView ns swap left right p,residual ns swap left right extra ch q⟩ :
      ScopedState ns.restricted p.handles) (sourceState ns swap left right extra ch q) := by
  cases h with
  | @accept rs r _ =>
    by_cases hroom : (rs++[r]).length < extra
    · have he : Process.afterAccepted extra (rs++[r]) = .input (rs++[r]) := if_pos hroom
      rw [he]; rfl
    · have he : Process.afterAccepted extra (rs++[r]) = .sendTally (rs++[r]) := if_neg hroom
      rw [he]; rfl
  | _ => rfl

end ExplainableCrypto.Helios.Symbolic.Historical.General
