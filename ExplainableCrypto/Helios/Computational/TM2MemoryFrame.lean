import ExplainableCrypto.Helios.Computational.TM2ReturnLink

/-! Preserve the caller's finite local memory while a TM2 subroutine uses its
own local memory. This changes neither stack operations nor transition count. -/
namespace ExplainableCrypto.Helios.Computational.TM2MemoryFrame
open Turing.TM2
variable {K L V W : Type*} {Γ : K → Type*} [DecidableEq K]

def liftStmt : Stmt Γ L V → Stmt Γ L (W × V)
  | .push k f q => .push k (fun v => f v.2) (liftStmt q)
  | .peek k f q => .peek k (fun v a => (v.1, f v.2 a)) (liftStmt q)
  | .pop k f q => .pop k (fun v a => (v.1, f v.2 a)) (liftStmt q)
  | .load f q => .load (fun v => (v.1, f v.2)) (liftStmt q)
  | .branch f a b => .branch (fun v => f v.2) (liftStmt a) (liftStmt b)
  | .goto f => .goto (fun v => f v.2)
  | .halt => .halt

def embed (saved : W) (cfg : Cfg Γ L V) : Cfg Γ L (W × V) :=
  ⟨cfg.l, (saved, cfg.var), cfg.stk⟩

theorem statement (stmt : Stmt Γ L V) (saved : W) (v : V) (tapes : ∀ k, List (Γ k)) :
    stepAux (liftStmt stmt) (saved, v) tapes = embed saved (stepAux stmt v tapes) := by
  induction stmt generalizing v tapes with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f a b ia ib => cases h : f v <;> simp [liftStmt, stepAux, h, ia, ib]
  | goto f => rfl
  | halt => rfl

theorem tick (code : L → Stmt Γ L V) (saved : W) (cfg : Cfg Γ L V) :
    TM2ReturnLink.tick (fun label => liftStmt (code label)) (embed saved cfg) =
      embed saved (TM2ReturnLink.tick code cfg) := by
  cases cfg with
  | mk label v tapes =>
    cases label with
    | none => rfl
    | some label => exact statement (code label) saved v tapes

theorem run (code : L → Stmt Γ L V) (saved : W) (fuel : Nat) (cfg : Cfg Γ L V) :
    (TM2ReturnLink.tick (fun label => liftStmt (code label)))^[fuel] (embed saved cfg) =
      embed saved ((TM2ReturnLink.tick code)^[fuel] cfg) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply, tick, ih, Function.iterate_succ_apply]

end ExplainableCrypto.Helios.Computational.TM2MemoryFrame
