import ExplainableCrypto.Helios.Computational.TM2TapeCost
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Literal two-stack controls for the reused tape translation. Expected words
and memory are derived directly from peek/push stack semantics. -/
namespace ExplainableCrypto.Helios.Computational.TM2TapeCostControls
open Turing TM2to1 TM2TapeCost

private def code : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
  fun _ => .peek 0 (fun _ b => b.getD false) (.push 1 id .halt)
private def words : Fin 2 → List Bool := ![[true, false, false], [false, true]]
private def columns : ListBlank (Fin 2 → Option Bool) :=
  ListBlank.mk [![some false, some true], ![some false, some false], ![some true, none]]
private def initial : Config (K := Fin 2) (Γ := fun _ => Bool) (Λ := Fin 1) (V := Bool) :=
  ⟨some (.normal 0), false, Tape.mk' ∅ (addBottom columns)⟩

private theorem presentation : ∀ k,
    columns.map (proj k) = ListBlank.mk ((words k).map some).reverse := by
  intro k
  fin_cases k <;> simp [columns, words, ListBlank.map_mk, proj]
  apply ListBlank.ext
  intro n
  rcases n with _ | _ | _ | n <;> rfl

/-- The source-step theorem applies to a constructed complete tape presentation. -/
theorem derived_step : ∃ used ≤ 25, ∃ out,
    TrCfg (TM2.stepAux (code 0) false words) out ∧ (tick code)^[used] initial = out := by
  have height : ∀ k, (words k).length ≤ 3 := by intro k; fin_cases k <;> decide
  have related : TrCfg (⟨some 0, false, words⟩ : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool)
      initial := ⟨columns, presentation⟩
  exact source_step code 0 false words 3 height initial related

/-- Sixteen actual translated ticks retain the source, push the observed top
onto the other stack, preserve the bottom marker and return there. -/
theorem actual_peek_push :
    let out := (tick code)^[16] initial
    out.l.isNone = true ∧ out.var = true ∧ out.Tape.head.1 = true ∧
    out.Tape.head.2 0 = some false ∧ out.Tape.head.2 1 = some true ∧
    (Tape.move Dir.right out.Tape).head.2 0 = some false ∧
    (Tape.move Dir.right out.Tape).head.2 1 = some false ∧
    ((Tape.move Dir.right)^[2] out.Tape).head.2 0 = some true ∧
    ((Tape.move Dir.right)^[2] out.Tape).head.2 1 = some true ∧
    ((Tape.move Dir.right)^[3] out.Tape).head.1 = false ∧
    ((Tape.move Dir.right)^[3] out.Tape).head.2 0 = none ∧
    ((Tape.move Dir.right)^[3] out.Tape).head.2 1 = none := by
  decide +kernel

/-- Constant three-tick stack-operation accounting cannot finish this example. -/
theorem constant_cost_not_enough :
    ((tick code)^[7] initial).l.isSome = true := by decide +kernel

/-- Statement depth counts stack accesses across both branches, even when finite
local memory chooses a short branch for a particular execution. -/
theorem branch_bound :
    accesses (TM2.Stmt.branch id (.halt : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool)
      (code 0)) = 2 ∧ work 3 (code 0) = 24 := by decide +kernel

/-- Empty peek/pop take the existing empty-stack branch and retain a different column. -/
theorem empty_peek_pop :
    let p : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
      fun _ => .peek 0 (fun _ b => b.getD false)
        (.pop 0 (fun _ b => b.getD true) .halt)
    let tape : ListBlank (Fin 2 → Option Bool) := ListBlank.mk [![none, some true]]
    let start : Config (K := Fin 2) (Γ := fun _ => Bool) (Λ := Fin 1) (V := Bool) :=
      ⟨some (.normal 0), true, Tape.mk' ∅ (addBottom tape)⟩
    let out := (tick p)^[5] start
    out.l.isNone = true ∧ out.var = true ∧ out.Tape.head.1 = true ∧
      out.Tape.head.2 0 = none ∧ out.Tape.head.2 1 = some true := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.TM2TapeCostControls
