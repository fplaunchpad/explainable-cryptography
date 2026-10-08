import ExplainableCrypto.Helios.Computational.BitOracleCanary
import VCVio.OracleComp.EvalDist

/-! Actual raw-oracle return linking. Intermediate halted padding is removed by
structural execution reasoning; only final halted configurations may be padded. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleReturnLink
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
variable {s l r m : Nat}

def embed (labels : Fin l → Fin r) (ret : Option (Fin r)) (cfg : Config s l m) : Config s r m :=
  ⟨cfg.l.elim ret (some ∘ labels),cfg.var,cfg.stk⟩

def stmt (labels : Fin l → Fin r) (ret : Option (Fin r)) :
    Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m) →
      Stmt (fun _ : Fin s => Bool) (Fin r) (Fin m)
  | .push k f q => .push k f (stmt labels ret q)
  | .peek k f q => .peek k f (stmt labels ret q)
  | .pop k f q => .pop k f (stmt labels ret q)
  | .load f q => .load f (stmt labels ret q)
  | .branch f a b => .branch f (stmt labels ret a) (stmt labels ret b)
  | .goto f => .goto (labels ∘ f)
  | .halt => ret.elim .halt (fun label => .goto (fun _ => label))

def command (labels : Fin l → Fin r) (ret : Option (Fin r)) : Command s l m → Command s r m
  | .compute q => .compute (stmt labels ret q)
  | .coin dest next => .coin dest (labels next)
  | .hash req dest next => .hash req dest (labels next)

private theorem stmt_step (labels : Fin l → Fin r) (ret : Option (Fin r))
    (q : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (v : Fin m) (words : Fin s → List Bool) :
    stepAux (stmt labels ret q) v words = embed labels ret (stepAux q v words) := by
  induction q generalizing v words with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f a b ia ib => cases h : f v <;> simp [stmt,stepAux,h,ia,ib]
  | goto f => rfl
  | halt => cases ret <;> rfl

private theorem stmt_cost (labels : Fin l → Fin r) (ret : Option (Fin r))
    (q : Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    localCost (stmt labels ret q) = localCost q := by
  induction q <;> simp_all [stmt,localCost]
  cases ret <;> rfl

private theorem step_live (p : Code s l m) (q : Code s r m)
    (labels : Fin l → Fin r) (ret : Option (Fin r))
    (hq : ∀ label, q (labels label) = command labels ret (p label))
    (label : Fin l) (v : Fin m) (words : Fin s → List Bool) :
    BitOracleMachine.step q (embed labels ret ⟨some label,v,words⟩) =
      (fun out => (embed labels ret out.1,out.2)) <$> BitOracleMachine.step p ⟨some label,v,words⟩ := by
  simp only [BitOracleMachine.step,embed,Option.elim,Function.comp_apply,hq]
  cases h : p label with
  | compute t => simp [command,stmt_step,stmt_cost,map_pure,embed,Option.elim]
  | coin dest next => simp [command,resume]
  | hash req dest next => simp [command,resume]

private theorem halted_run (p : Code s l m) (fuel : Nat) (v : Fin m)
    (words : Fin s → List Bool) :
    BitOracleMachine.run p fuel ⟨none,v,words⟩ = pure (⟨none,v,words⟩,0) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [BitOracleMachine.run,BitOracleMachine.step,ih]

/-- Split the actual charged execution at a fixed clock boundary. -/
theorem run_add (p : Code s l m) (a b : Nat) (cfg : Config s l m) :
    BitOracleMachine.run p (a+b) cfg = (do
      let first ← BitOracleMachine.run p a cfg
      let last ← BitOracleMachine.run p b first.1
      pure (last.1,first.2+last.2)) := by
  induction a generalizing cfg with
  | zero => simp [BitOracleMachine.run]
  | succ a ih => simp [Nat.succ_add,BitOracleMachine.run,ih,bind_assoc,Nat.add_assoc]

/-- Padding preserves a run only after every reachable result has halted. -/
theorem padded (p : Code s l m) (fuel extra : Nat) (cfg : Config s l m)
    (hh : ∀ out ∈ support (BitOracleMachine.run p fuel cfg), out.1.l = none) :
    BitOracleMachine.run p (extra+fuel) cfg = BitOracleMachine.run p fuel cfg := by
  rw [Nat.add_comm extra fuel,run_add]
  conv_rhs => rw [← bind_pure (x := BitOracleMachine.run p fuel cfg)]
  apply bind_congr_of_forall_mem_support
  intro out ho
  rcases out with ⟨⟨label,v,words⟩,charge⟩
  have hl := hh _ ho
  dsimp only at hl
  subst label
  simp [halted_run]

/-- Renaming with a final halt preserves the entire run, including every charge. -/
theorem rename_run (p : Code s l m) (q : Code s r m) (labels : Fin l → Fin r)
    (hq : ∀ label, q (labels label) = command labels none (p label))
    (fuel : Nat) (cfg : Config s l m) :
    BitOracleMachine.run q fuel (embed labels none cfg) =
      (fun out => (embed labels none out.1,out.2)) <$> BitOracleMachine.run p fuel cfg := by
  induction fuel generalizing cfg with
  | zero => simp [BitOracleMachine.run]
  | succ fuel ih =>
    rcases cfg with ⟨label,v,words⟩
    cases label with
    | none => simp [embed,halted_run]
    | some label =>
      rw [BitOracleMachine.run,step_live p q labels none hq]
      simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
      simp only [BitOracleMachine.run,bind_assoc,pure_bind]
      apply bind_congr
      intro first
      rw [ih]
      simp [map_eq_bind_pure_comp,bind_assoc]

private theorem tail_support (p : Code s l m) (fuel : Nat) (cfg : Config s l m)
    (first last : Config s l m × Nat) (hf : first ∈ support (BitOracleMachine.step p cfg))
    (hl : last ∈ support (BitOracleMachine.run p fuel first.1)) :
    (last.1,first.2+last.2) ∈ support (BitOracleMachine.run p (fuel+1) cfg) := by
  rw [BitOracleMachine.run,mem_support_bind_iff]
  refine ⟨first,hf,?_⟩
  rw [mem_support_bind_iff]
  exact ⟨last,hl,by simp⟩

/-- A source whose reachable leaves halt and a halting continuation compose in
one uninterrupted program. The two assumptions concern actual run supports;
callers must derive them from their source and continuation theorems. -/
theorem run (p : Code s l m) (q : Code s r m) (labels : Fin l → Fin r) (ret : Fin r)
    (hq : ∀ label, q (labels label) = command labels (some ret) (p label))
    (fuel extra : Nat) (cfg : Config s l m)
    (hh : ∀ out ∈ support (BitOracleMachine.run p fuel cfg), out.1.l = none)
    (hc : ∀ out ∈ support (BitOracleMachine.run p fuel cfg),
      ∀ last ∈ support (BitOracleMachine.run q extra (embed labels (some ret) out.1)),
        last.1.l = none) :
    BitOracleMachine.run q (fuel+extra) (embed labels (some ret) cfg) = (do
      let first ← BitOracleMachine.run p fuel cfg
      let last ← BitOracleMachine.run q extra (embed labels (some ret) first.1)
      pure (last.1,first.2+last.2)) := by
  induction fuel generalizing cfg with
  | zero => simp [BitOracleMachine.run]
  | succ fuel ih =>
    rcases cfg with ⟨label,v,words⟩
    cases label with
    | none =>
      have hp := hc (⟨none,v,words⟩,0) (by simp [halted_run])
      rw [halted_run]
      simp only [pure_bind,Nat.zero_add,Prod.mk.eta,bind_pure]
      exact padded q extra (fuel+1) _ hp
    | some label =>
      rw [Nat.succ_add,BitOracleMachine.run,step_live p q labels (some ret) hq]
      simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
      simp only [BitOracleMachine.run,bind_assoc,pure_bind]
      apply bind_congr_of_forall_mem_support
      intro first hf
      have hh' : ∀ last ∈ support (BitOracleMachine.run p fuel first.1), last.1.l = none := by
        intro last hl
        exact hh (last.1,first.2+last.2) (tail_support p fuel _ first last hf hl)
      have hc' : ∀ last ∈ support (BitOracleMachine.run p fuel first.1),
          ∀ done ∈ support (BitOracleMachine.run q extra (embed labels (some ret) last.1)),
            done.1.l = none := by
        intro last hl
        exact hc (last.1,first.2+last.2) (tail_support p fuel _ first last hf hl)
      rw [ih first.1 hh' hc']
      simp [Nat.add_assoc]

end ExplainableCrypto.Helios.Computational.BitOracleReturnLink
