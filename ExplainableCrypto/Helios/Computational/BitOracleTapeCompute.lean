import ExplainableCrypto.Helios.Computational.TM2TapeRuns
import ExplainableCrypto.Helios.Computational.BitOraclePortTransfer

/-! Execute one ordinary source statement before returning to the oracle loop.
Its result label is finite saved memory; the actual subroutine halts. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeCompute
open Turing TM2TapeRuns BitOraclePortTransfer

private def closeStmt {K L V : Type} {Γ : K → Type} :
    TM2.Stmt Γ L V → TM2.Stmt Γ Unit (Option L × V)
  | .push k f q => .push k (fun v => f v.2) (closeStmt q)
  | .peek k f q => .peek k (fun v a => (v.1, f v.2 a)) (closeStmt q)
  | .pop k f q => .pop k (fun v a => (v.1, f v.2 a)) (closeStmt q)
  | .load f q => .load (fun v => (v.1, f v.2)) (closeStmt q)
  | .branch f a b => .branch (fun v => f v.2) (closeStmt a) (closeStmt b)
  | .goto f => .load (fun v => (some (f v.2), v.2)) .halt
  | .halt => .load (fun v => (none, v.2)) .halt

private def closed {K L V : Type} {Γ : K → Type}
    (c : TM2.Cfg Γ L V) : TM2.Cfg Γ Unit (Option L × V) :=
  ⟨none, (c.l, c.var), c.stk⟩

private theorem close_statement {K L V : Type} {Γ : K → Type} [DecidableEq K]
    (q : TM2.Stmt Γ L V) (saved : Option L) (v : V) (words : ∀ k, List (Γ k)) :
    TM2.stepAux (closeStmt q) (saved, v) words = closed (TM2.stepAux q v words) := by
  induction q generalizing saved v words with
  | push k f q ih => exact ih _ _ _
  | peek k f q ih => exact ih _ _ _
  | pop k f q ih => exact ih _ _ _
  | load f q ih => exact ih _ _ _
  | branch f a b ia ib => cases h : f v <;> simp [closeStmt, TM2.stepAux, h, ia, ib]
  | goto f => rfl
  | halt => rfl

private theorem close_accesses {K L V : Type} {Γ : K → Type} (q : TM2.Stmt Γ L V) :
    TM2TapeCost.accesses (closeStmt q) = TM2TapeCost.accesses q := by
  induction q <;> simp_all [closeStmt, TM2TapeCost.accesses]

/-- The ready caller has the original stacks and two empty private columns. -/
def framed {s l m : Nat} (c : BitOracleMachine.Config s l m) :
    TM2.Cfg (fun _ : Ports s => Bool) (Fin l) (Fin m) :=
  TM2StackFrame.embed (Equiv.refl _) c (fun _ => [])

/-- Relocate only original ports and return through finite local memory. -/
def compile {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    TM2.Stmt (fun _ : Ports s => Bool) Unit (Option (Fin l) × Fin m) :=
  closeStmt (TM2StackFrame.relocate (Equiv.refl _) q)

abbrev Config (s l m : Nat) := TM2TapeCost.Config (K := Ports s)
  (Γ := fun _ => Bool) (Λ := Unit) (V := Option (Fin l) × Fin m)

/-- Canonical entry is data for the correspondence; the loop reuses its actual tape. -/
def entry {s l m : Nat} (c : BitOracleMachine.Config s l m) :
    TM2.Cfg (fun _ : Ports s => Bool) Unit (Option (Fin l) × Fin m) :=
  ⟨some (), (c.l, c.var), (framed c).stk⟩

/-- Finite return context and the unchanged representation of the resulting stacks. -/
def result {s l m : Nat} (c : BitOracleMachine.Config s l m) :
    TM2.Cfg (fun _ : Ports s => Bool) Unit (Option (Fin l) × Fin m) :=
  ⟨none, (c.l, c.var), (framed c).stk⟩

/-- Actual local statement execution retains both private columns and stores
the original resulting label and memory before halting. -/
theorem statement {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (c : BitOracleMachine.Config s l m) :
    TM2.stepAux (compile q) (c.l, c.var) (framed c).stk =
      result (TM2.stepAux q c.var c.stk) := by
  rw [compile, close_statement]
  exact congrArg closed (TM2StackFrame.statement (Equiv.refl _) q c.var c.stk (fun _ => []))

/-- Return handling adds no stack accesses. Finite local syntax costs remain
part of the separate primitive-cost transfer obligation. -/
theorem accesses {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    TM2TapeCost.accesses (compile q) = TM2TapeCost.accesses q := by
  rw [compile, close_accesses]
  induction q <;> simp_all [TM2StackFrame.relocate, TM2TapeCost.accesses]

/-- An actual bounded TM1 run returns the exact source result. The initial
presentation, final tape and private frame are derived from the source. -/
theorem run {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (c : BitOracleMachine.Config s l m) :
    let a := TM2TapeCost.accesses q
    let H := height (framed c).stk
    ∃ used ≤ 1 + a * (2 * (H + a) + 2),
      (TM2TapeCost.tick (fun _ : Unit => compile q))^[used] (pack (entry c)) =
        pack (result (TM2.stepAux q c.var c.stk)) := by
  dsimp only
  obtain ⟨used, hu, out, ho, he⟩ := TM2TapeCost.source_step
    (fun _ : Unit => compile q) () (c.l, c.var) (framed c).stk
    (height (framed c).stk) (length_le_height (framed c).stk)
    (pack (entry c)) (pack_related (entry c))
  rw [statement] at ho
  refine ⟨used, ?_, he.trans (related_unique _ _ _ ho (pack_related _))⟩
  simpa only [TM2TapeCost.work, accesses] using hu

end ExplainableCrypto.Helios.Computational.BitOracleTapeCompute
