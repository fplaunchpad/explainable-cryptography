import ExplainableCrypto.Helios.Computational.BitOracleMachine

/-! Executable finite coordinate changes shared by division and scalar writing.
Every configuration and step is retained; no arithmetic runs in the adapter. -/
namespace ExplainableCrypto.Helios.Computational.TM2FiniteCoordinates
open Turing.TM2
variable {K L V : Type*} [DecidableEq K] {k l m : Nat}
variable (ports : K ≃ Fin k) (labels : L ≃ Fin l) (memory : V ≃ Fin m)

def data (words : K → List Bool) : Fin k → List Bool :=
  fun k => words (ports.symm k)

def present (cfg : Cfg (fun _ : K => Bool) L V) : BitOracleMachine.Config k l m :=
  ⟨cfg.l.map labels, memory cfg.var, data ports cfg.stk⟩

def translate : Stmt (fun _ : K => Bool) L V →
    Stmt (fun _ : Fin k => Bool) (Fin l) (Fin m)
  | .push k f s => .push (ports k) (fun v => f (memory.symm v)) (translate s)
  | .peek k f s => .peek (ports k) (fun v b => memory (f (memory.symm v) b)) (translate s)
  | .pop k f s => .pop (ports k) (fun v b => memory (f (memory.symm v) b)) (translate s)
  | .load f s => .load (fun v => memory (f (memory.symm v))) (translate s)
  | .branch f a b => .branch (fun v => f (memory.symm v)) (translate a) (translate b)
  | .goto f => .goto (fun v => labels (f (memory.symm v)))
  | .halt => .halt

def program (source : L → Stmt (fun _ : K => Bool) L V) (label : Fin l) : Stmt (fun _ : Fin k => Bool) (Fin l) (Fin m) :=
  translate ports labels memory (source (labels.symm label))

theorem data_update (words : K → List Bool) (k : K)
    (word : List Bool) :
    data ports (Function.update words k word) = Function.update (data ports words) (ports k) word := by
  funext j
  obtain ⟨x,rfl⟩ := ports.surjective j
  simp [data, Function.update, ports.injective.eq_iff]

theorem statement (s : Stmt (fun _ : K => Bool) L V)
    (v : V) (words : K → List Bool) :
    stepAux (translate ports labels memory s) (memory v) (data ports words) = present ports labels memory (stepAux s v words) := by
  induction s generalizing v words with
  | push k f s ih => simpa only [translate, stepAux, Equiv.symm_apply_apply, data,
      ← data_update] using ih v (Function.update words k (f v :: words k))
  | peek k f s ih =>
    simpa only [translate, stepAux, Equiv.symm_apply_apply, data] using
      ih (f v (words k).head?) words
  | pop k f s ih => simpa only [translate, stepAux, Equiv.symm_apply_apply, data,
      ← data_update] using ih (f v (words k).head?) (Function.update words k (words k).tail)
  | load f s ih => simpa only [translate, stepAux, Equiv.symm_apply_apply] using ih (f v) words
  | branch f a b ia ib => cases h : f v <;> simp [translate, stepAux, h, ia, ib]
  | goto f => simp [translate, stepAux, present]
  | halt => rfl

/-- All configurations, including intermediate scratch contents, translate exactly. -/
theorem tick (source : L → Stmt (fun _ : K => Bool) L V) (cfg : Cfg (fun _ : K => Bool) L V) :
    TM2ReturnLink.tick (program ports labels memory source) (present ports labels memory cfg) = present ports labels memory (TM2ReturnLink.tick source cfg) := by
  cases cfg with
  | mk label v words => cases label with
    | none => rfl
    | some label => simpa only [TM2ReturnLink.tick,
        present, step, Option.map_some, program, Equiv.symm_apply_apply, Option.getD_some]
        using statement ports labels memory (source label) v words

/-- Entire original executions retain their transition count and full frame. -/
theorem run (source : L → Stmt (fun _ : K => Bool) L V) (fuel : Nat) (cfg : Cfg (fun _ : K => Bool) L V) :
    (TM2ReturnLink.tick (program ports labels memory source))^[fuel] (present ports labels memory cfg) =
      present ports labels memory ((TM2ReturnLink.tick source)^[fuel] cfg) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply, tick, ih, Function.iterate_succ_apply]

end ExplainableCrypto.Helios.Computational.TM2FiniteCoordinates
