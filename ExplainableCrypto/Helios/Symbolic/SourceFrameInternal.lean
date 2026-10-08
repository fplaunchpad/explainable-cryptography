import ExplainableCrypto.Helios.Symbolic.SourceFrameInput

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {restricted : Finset Nat} {handles : Nat}

/-- Existing ground core reductions derive in any free-variable domain, so
public active handles can remain beside the evaluated election body. -/
theorem coreStep_ground_derivable (V : Type) {p q : Agent Empty} (h : Agent.CoreStep p q) :
    Reduction (.plain (groundAgent p : Agent V)) (.plain (groundAgent q)) := by
  induction h with
  | comm c m p q =>
    have hs := message_communication c (groundTerm m : Term V) (groundAgent p)
      (q.subst (liftSubst (Empty.elim : Empty → Term V)))
    simpa only [groundTerm,groundAgent,Agent.subst,Agent.bind_subst] using hs
  | thenBranch f p q hf => exact Reduction.thenBranch f (groundAgent p) (groundAgent q) hf
  | elseBranch f p q hf => exact Reduction.elseBranch f (groundAgent p) (groundAgent q) hf
  | parLeft q _ ih => exact ih.plain_parLeft (groundAgent q)
  | parRight p _ ih => exact ih.plain_parRight (groundAgent p)

theorem tau_ground_derivable (V : Type) {p q : Agent Empty} (h : Agent.Tau p q) :
    Reduction (.plain (groundAgent p : Agent V)) (.plain (groundAgent q)) := by
  obtain ⟨p',q',hp,hc,hq⟩ := h
  exact .congr (parEq_derivable (hp.subst Empty.elim)) (coreStep_ground_derivable V hc)
    (parEq_derivable (hq.subst Empty.elim))

/-- Every evaluated internal step retains its actual public active frame in
the explicit atomic/active source derivation. -/
theorem scoped_tau_derivable (hidden : Finset Nat) (p q : ScopedState restricted handles)
    (h : ScopedStep hidden restricted p .tau q) :
    Reduction (frameProcess p.frame p.body) (frameProcess q.frame q.body) := by
  obtain ⟨he,ht⟩ := (scoped_tau_iff p q).mp h
  rw [← he]
  exact .parRight (activeFrame p.frame) (tau_ground_derivable (Fin handles) ht)
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
