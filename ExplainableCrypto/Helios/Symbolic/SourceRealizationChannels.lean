import ExplainableCrypto.Helios.Symbolic.SourceChannelScope
import ExplainableCrypto.Helios.Symbolic.SourceSameRealizations

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Agent
variable {V : Type}

theorem ParEq.channels {p q : Agent V} (h : ParEq p q) : p.channels = q.channels := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h j ih ij => exact ih.trans ij
  | zero => simp [Agent.channels]
  | assoc => exact Finset.union_assoc _ _ _
  | comm => exact Finset.union_comm _ _
  | par h j ih ij => simp only [Agent.channels,ih,ij]

theorem EquivE.channels {p q : Agent V} (h : EquivE p q) : p.channels = q.channels := by
  induction h <;> simp_all only [Agent.channels]

theorem EvalEq.channels {p q : Agent V} (h : EvalEq p q) : p.channels = q.channels := by
  obtain ⟨r,hp,he⟩ := h
  exact hp.channels.trans he.channels
end Agent

namespace Extended
variable {V : Type}

/-- Complete realization retains all syntactic channels, including guarded
continuations and both branches; active equations only constrain base terms. -/
theorem Realizes.channels {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (h : a.Realizes env p) : a.channels = p.channels := by
  induction a generalizing p with
  | plain q => exact (Agent.channels_subst q env).symm.trans (Agent.EvalEq.channels h)
  | active x m => exact Agent.EvalEq.channels h.2
  | par a b ha hb =>
    obtain ⟨q,r,hq,hr,he⟩ := h
    exact (congrArg₂ (fun x y : Finset Nat => x ∪ y) (ha hq) (hb hr)).trans (Agent.EvalEq.channels he)
  | newVar a ih => obtain ⟨m,hm⟩ := h; exact ih hm

/-- A nonempty complete realization class determines channel support. The
existence premise is necessary for inconsistent active equations. -/
theorem SameRealizations.channels {a b : Extended V} (h : a.SameRealizations b)
    {env : V → Ground} {p : Agent Empty} (hr : a.Realizes env p) : a.channels = b.channels :=
  hr.channels.trans ((h env p).mp hr).channels.symm
end Extended
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
