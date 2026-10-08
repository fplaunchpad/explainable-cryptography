import ExplainableCrypto.Helios.Computational.TM2ReturnLink

/-! Relocate binary-stack instructions into a larger finite layout. The extra
stacks form an explicit frame; every transition and its fuel are preserved. -/
namespace ExplainableCrypto.Helios.Computational.TM2StackFrame
open Turing.TM2
variable {K E J L V : Type*} [DecidableEq K] [DecidableEq J]

def data (layout : K ⊕ E ≃ J) (work : K → List Bool) (frame : E → List Bool) :
    J → List Bool := fun j => (layout.symm j).elim work frame

def embed (layout : K ⊕ E ≃ J) (c : Cfg (fun _ : K => Bool) L V)
    (frame : E → List Bool) : Cfg (fun _ : J => Bool) L V :=
  ⟨c.l,c.var,data layout c.stk frame⟩

def relocate (layout : K ⊕ E ≃ J) :
    Stmt (fun _ : K => Bool) L V → Stmt (fun _ : J => Bool) L V
  | .push k f s => .push (layout (.inl k)) f (relocate layout s)
  | .peek k f s => .peek (layout (.inl k)) f (relocate layout s)
  | .pop k f s => .pop (layout (.inl k)) f (relocate layout s)
  | .load f s => .load f (relocate layout s)
  | .branch f a b => .branch f (relocate layout a) (relocate layout b)
  | .goto f => .goto f
  | .halt => .halt

private theorem data_update (layout : K ⊕ E ≃ J) (work : K → List Bool)
    (frame : E → List Bool) (k : K) (word : List Bool) :
    data layout (Function.update work k word) frame =
      Function.update (data layout work frame) (layout (.inl k)) word := by
  funext j
  obtain ⟨x,rfl⟩ := layout.surjective j
  cases x with
  | inl a => simp [data,Function.update,layout.injective.eq_iff]
  | inr a => simp [data,Function.update,layout.injective.eq_iff]

/-- Relocation preserves an actual statement's complete result and the frame. -/
theorem statement (layout : K ⊕ E ≃ J) (s : Stmt (fun _ : K => Bool) L V)
    (v : V) (work : K → List Bool) (frame : E → List Bool) :
    stepAux (relocate layout s) v (data layout work frame) =
      embed layout (stepAux s v work) frame := by
  induction s generalizing v work with
  | push k f s ih =>
    simpa only [relocate,stepAux,data,Equiv.symm_apply_apply,Sum.elim_inl,←data_update] using
      ih v (Function.update work k (f v :: work k))
  | peek k f s ih =>
    simpa only [relocate,stepAux,data,Equiv.symm_apply_apply,Sum.elim_inl] using
      ih (f v (work k).head?) work
  | pop k f s ih =>
    simpa only [relocate,stepAux,data,Equiv.symm_apply_apply,Sum.elim_inl,←data_update] using
      ih (f v (work k).head?) (Function.update work k (work k).tail)
  | load f s ih => exact ih _ _
  | branch f a b ia ib => cases h : f v <;> simp [relocate,stepAux,h,ia,ib]
  | goto f => rfl
  | halt => rfl

/-- The fixed-halt step commutes exactly, on all states and frames. -/
theorem tick (layout : K ⊕ E ≃ J) (p : L → Stmt (fun _ : K => Bool) L V)
    (c : Cfg (fun _ : K => Bool) L V) (frame : E → List Bool) :
    TM2ReturnLink.tick (fun l => relocate layout (p l)) (embed layout c frame) =
      embed layout (TM2ReturnLink.tick p c) frame := by
  cases c with
  | mk l v work =>
    cases l with
    | none => rfl
    | some l => exact statement layout (p l) v work frame

theorem run (layout : K ⊕ E ≃ J) (p : L → Stmt (fun _ : K => Bool) L V)
    (fuel : Nat) (c : Cfg (fun _ : K => Bool) L V) (frame : E → List Bool) :
    (TM2ReturnLink.tick (fun l => relocate layout (p l)))^[fuel] (embed layout c frame) =
      embed layout ((TM2ReturnLink.tick p)^[fuel] c) frame := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply,tick,ih,Function.iterate_succ_apply]

omit [DecidableEq K] [DecidableEq J] in
theorem supports (layout : K ⊕ E ≃ J) (S : Finset L)
    (s : Stmt (fun _ : K => Bool) L V) :
    SupportsStmt S (relocate layout s) ↔ SupportsStmt S s := by
  induction s <;> simp_all [relocate,SupportsStmt]

#print axioms statement
#print axioms tick
#print axioms run
#print axioms supports
end ExplainableCrypto.Helios.Computational.TM2StackFrame
