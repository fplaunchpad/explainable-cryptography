import ExplainableCrypto.Helios.Computational.TM2TapeRuns

/-! Quantitative execution through Mathlib's existing TM1-to-TM0 compiler.
The target transitions are physical single moves/writes. Finite support is
explicit; no runtime callback or alternative machine translation is added. -/
namespace ExplainableCrypto.Helios.Computational.TM1PrimitiveCost
open Turing Function
variable {Γ Λ V : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited V]

/-- Maximum primitive moves/writes along a statement branch. The compiler
folds finite head/control loads and branches into its transition table. -/
def allowance : TM1.Stmt Γ Λ V → Nat
  | .move _ q | .write _ q => 1 + allowance q
  | .load _ q => allowance q
  | .branch _ a b => max (allowance a) (allowance b)
  | .goto _ | .halt => 1

/-- Exact physical work of this statement on the given full configuration. -/
def work : TM1.Stmt Γ Λ V → V → Tape Γ → Nat
  | .move d q, v, tape => 1 + work q v (tape.move d)
  | .write f q, v, tape => 1 + work q v (tape.write (f tape.1 v))
  | .load f q, v, tape => work q (f tape.1 v) tape
  | .branch p a b, v, tape => if p tape.1 v then work a v tape else work b v tape
  | .goto _, _, _ | .halt, _, _ => 1

def tick (M : Λ → TM1.Stmt Γ Λ V) (cfg : TM0.Cfg Γ (TM1to0.Λ' M)) :=
  (TM0.step (TM1to0.tr M) cfg).getD cfg

omit [Inhabited Λ] [Inhabited V] in
private theorem work_pos (q : TM1.Stmt Γ Λ V) (v : V) (tape : Tape Γ) :
    0 < work q v tape := by
  induction q generalizing v tape with
  | move _ _ ih | write _ _ ih => simp only [work]; omega
  | load _ _ ih => exact ih _ _
  | branch p _ _ ha hb => simp only [work]; split <;> first | apply ha | apply hb
  | goto | halt => exact Nat.zero_lt_one

omit [Inhabited Λ] [Inhabited V] in
/-- The exact branch work is bounded independently of tape contents. -/
theorem work_le (q : TM1.Stmt Γ Λ V) (v : V) (tape : Tape Γ) :
    work q v tape ≤ allowance q := by
  induction q generalizing v tape with
  | move _ _ ih | write _ _ ih => exact Nat.add_le_add_left (ih _ _) 1
  | load _ _ ih => exact ih _ _
  | branch p a b ha hb =>
    simp only [work, allowance]
    split
    · exact le_trans (ha _ _) (Nat.le_max_left _ _)
    · exact le_trans (hb _ _) (Nat.le_max_right _ _)
  | goto | halt => exact le_rfl

private theorem iterate_of_tick_eq {A : Type*} (f : A → A) (a b : A)
    (n : Nat) (hn : 0 < n) (h : f a = f b) : f^[n] a = f^[n] b := by
  cases n with
  | zero => omega
  | succ n => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h]

/-- Exact complete-state execution through the unchanged primitive compiler. -/
theorem statement (M : Λ → TM1.Stmt Γ Λ V) (q : TM1.Stmt Γ Λ V)
    (v : V) (tape : Tape Γ) :
    (tick M)^[work q v tape] ⟨(some q, v), tape⟩ =
      TM1to0.trCfg M (TM1.stepAux q v tape) := by
  induction q generalizing v tape with
  | move d q ih =>
    rw [work, Nat.add_comm, Function.iterate_succ_apply]
    exact ih _ _
  | write f q ih =>
    rw [work, Nat.add_comm, Function.iterate_succ_apply]
    exact ih _ _
  | load f q ih =>
    have h := iterate_of_tick_eq (tick M)
      ⟨(some (.load f q), v), tape⟩ ⟨(some q, f tape.1 v), tape⟩
      (work q (f tape.1 v) tape) (work_pos _ _ _) rfl
    exact h.trans (ih _ _)
  | branch p a b ha hb =>
    cases hp : p tape.1 v
    · simp only [work, hp, Bool.false_eq_true, ↓reduceIte, TM1.stepAux, Bool.cond_false]
      have h := iterate_of_tick_eq (tick M)
        ⟨(some (.branch p a b), v), tape⟩ ⟨(some b, v), tape⟩
        (work b v tape) (work_pos _ _ _) (by simp [tick, TM0.step, TM1to0.tr, TM1to0.trAux, hp])
      exact h.trans (hb _ _)
    · simp only [work, hp, ↓reduceIte, TM1.stepAux, Bool.cond_true]
      have h := iterate_of_tick_eq (tick M)
        ⟨(some (.branch p a b), v), tape⟩ ⟨(some a, v), tape⟩
        (work a v tape) (work_pos _ _ _) (by simp [tick, TM0.step, TM1to0.tr, TM1to0.trAux, hp])
      exact h.trans (ha _ _)
  | goto f => simp [work, tick, TM0.step, TM1to0.tr, TM1to0.trAux,
      TM1to0.trCfg, TM1.stepAux, Tape.write_self]
  | halt => simp [work, tick, TM0.step, TM1to0.tr, TM1to0.trAux,
      TM1to0.trCfg, TM1.stepAux, Tape.write_self]

/-- The multiplier depends only on the fixed supported program. -/
noncomputable def multiplier (M : Λ → TM1.Stmt Γ Λ V) (support : Finset Λ) : Nat :=
  support.sup (fun label => allowance (M label))

/-- All finite supported TM1 runs have a code-derived primitive execution
bound, including halted suffixes. Complete target tape and memory agree. -/
theorem run (M : Λ → TM1.Stmt Γ Λ V) (support : Finset Λ)
    (hs : TM1.Supports M support) (fuel : Nat) (cfg : TM1.Cfg Γ Λ V)
    (hc : cfg.l ∈ Finset.insertNone support) :
    ∃ used ≤ fuel * multiplier M support,
      (tick M)^[used] (TM1to0.trCfg M cfg) = TM1to0.trCfg M
        ((fun c => (TM1.step M c).getD c)^[fuel] cfg) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨0, Nat.zero_le _, rfl⟩
  | succ fuel ih =>
    cases cfg with
    | mk label v tape =>
      cases label with
      | none =>
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [Function.iterate_fixed (f := fun c => (TM1.step M c).getD c)
          (x := ⟨none, v, tape⟩) rfl]
        rfl
      | some label =>
        have hn := TM1.step_supports M hs
          (c := ⟨some label, v, tape⟩) (c' := TM1.stepAux (M label) v tape) rfl hc
        obtain ⟨used, hu, he⟩ := ih _ hn
        have ha : work (M label) v tape ≤ multiplier M support :=
          le_trans (work_le _ _ _) (Finset.le_sup (f := fun label => allowance (M label))
            (Finset.some_mem_insertNone.mp hc))
        refine ⟨work (M label) v tape + used, ?_, ?_⟩
        · rw [Nat.succ_mul]; omega
        · rw [Nat.add_comm, Function.iterate_add_apply]
          change (tick M)^[used] ((tick M)^[work (M label) v tape]
            ⟨(some (M label), v), tape⟩) = _
          rw [statement, he, Function.iterate_succ_apply]
          rfl

end ExplainableCrypto.Helios.Computational.TM1PrimitiveCost
