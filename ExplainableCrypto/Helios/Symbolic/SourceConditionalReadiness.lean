import ExplainableCrypto.Helios.Symbolic.SourceCommunicationInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
variable {V W : Type}

/-- A conditional at evaluation depth, without crossing an input/output prefix.
This records syntax only and does not authorize either branch. -/
def HasConditional : Agent V → Prop
  | .par p q => HasConditional p ∨ HasConditional q
  | .branch _ _ _ => True
  | _ => False

theorem hasConditional_subst (p : Agent V) (σ : V → Term W) :
    (p.subst σ).HasConditional ↔ p.HasConditional := by
  induction p <;> simp_all [Agent.subst,HasConditional]

theorem hasConditional_mapNames (p : Agent V) (f g : Nat → Nat) :
    (p.mapNames f g).HasConditional ↔ p.HasConditional := by
  induction p <;> simp_all [Agent.mapNames,HasConditional]

theorem ParEq.hasConditional {p q : Agent V} (h : ParEq p q) :
    p.HasConditional ↔ q.HasConditional := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h j ih ij => exact ih.trans ij
  | zero => simp [HasConditional]
  | assoc => exact or_assoc
  | comm => exact or_comm
  | par h j ih ij => exact or_congr ih ij

theorem EquivE.hasConditional {p q : Agent V} (h : EquivE p q) :
    p.HasConditional ↔ q.HasConditional := by
  induction h <;> simp_all [HasConditional]

theorem EvalEq.hasConditional {p q : Agent V} (h : EvalEq p q) :
    p.HasConditional ↔ q.HasConditional := by
  obtain ⟨r,hp,hq⟩ := h
  exact hp.hasConditional.trans hq.hasConditional

theorem hasConditional_iff_prefix (p : Agent V) :
    p.HasConditional ↔ ∃ f a b, Agent.branch f a b ∈ p.threads := by
  induction p with
  | nil => simp [HasConditional,threads,threadList]
  | par p q hp hq => simp only [HasConditional,hp,hq,threads_par,Multiset.mem_add,exists_or]
  | output => simp [HasConditional,threads,threadList]
  | input => simp [HasConditional,threads,threadList]
  | branch => simp [HasConditional,threads,threadList]

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Agent
