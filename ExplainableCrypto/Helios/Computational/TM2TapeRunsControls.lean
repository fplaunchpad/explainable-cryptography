import ExplainableCrypto.Helios.Computational.TM2TapeRuns
import Mathlib.Data.Fin.VecNotation

/-! Independent literal controls: repeated pushes cost 4+6+8+10 ticks;
source stack order differs from bottom-to-top tape order. -/
namespace ExplainableCrypto.Helios.Computational.TM2TapeRunsControls
open Turing TM2to1 TM2TapeCost TM2TapeRuns

private def grow : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
  fun _ => .push 0 id (.goto (fun _ => 0))
private def empty : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
  ⟨some 0, true, ![[], []]⟩

/-- Apply the general theorem without any presentation or height certificate. -/
theorem derived_growing_run : ∃ used ≤ 44,
    (tick grow)^[used] (pack empty) = pack ((TM2ReturnLink.tick grow)^[4] empty) ∧
    ∀ k, (((TM2ReturnLink.tick grow)^[4] empty).stk k).length ≤ 4 := by
  have hc : codeAccesses grow = 1 := by decide +kernel
  have hh : height empty.stk = 0 := by decide +kernel
  simpa only [hc, hh] using run_packed grow 4 empty

/-- Four pushes execute on one persistent tape in 28 ticks. -/
theorem actual_growing_run :
    let out := (tick grow)^[28] (pack empty)
    out.l.map (fun | .normal _ => true | _ => false) = some true ∧
    out.Tape.head.1 = true ∧ out.Tape.head.2 0 = some true ∧
    (Tape.move Dir.right out.Tape).head.2 0 = some true ∧
    ((Tape.move Dir.right)^[2] out.Tape).head.2 0 = some true ∧
    ((Tape.move Dir.right)^[3] out.Tape).head.2 0 = some true ∧
    ((Tape.move Dir.right)^[4] out.Tape).head.2 0 = none ∧
    out.Tape.head.2 1 = none := by decide +kernel

/-- Freezing the initial height yields 20 ticks, which stops inside the fourth push. -/
theorem frozen_height_fails : ¬ ∃ used ≤ 20,
    (tick grow)^[used] (pack empty) = pack ((TM2ReturnLink.tick grow)^[4] empty) := by
  have check : ∀ n : Fin 21,
      let out := (tick grow)^[n.val] (pack empty)
      out.l.map (fun | .normal _ => true | _ => false) = some true →
        ((Tape.move Dir.right)^[3] out.Tape).head.2 0 = none := by decide +kernel
  rintro ⟨used, hu, he⟩
  have h := check ⟨used, by omega⟩
  dsimp only at h
  rw [he] at h
  have impossible := h (by decide +kernel)
  change some true = none at impossible
  cases impossible

/-- Reversal is observable on a nonpalindrome: canonical packing reads the true
source top, while unreversed columns return false. The other column survives. -/
theorem packing_order_matters :
    let code : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
      fun _ => .peek 0 (fun _ b => b.getD false) .halt
    let src : TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool :=
      ⟨some 0, false, ![[true, false, false], [false]]⟩
    let wrong : TM2TapeCost.Config (K := Fin 2) (Γ := fun _ => Bool)
        (Λ := Fin 1) (V := Bool) :=
      ⟨some (.normal 0), false, Tape.mk' ∅ (addBottom (ListBlank.mk
        [![some true, some false], ![some false, none], ![some false, none]]))⟩
    let good := (tick code)^[9] (pack src)
    good.l.isNone = true ∧ good.var = true ∧ good.Tape.head.2 1 = some false ∧
    ((tick code)^[9] wrong).var = false := by decide +kernel

/-- Source halt padding needs no extra tape transitions after reaching halt. -/
theorem early_halt :
    let code : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool := fun _ => .halt
    ∃ used ≤ 9, (tick code)^[used] (pack empty) =
      pack ((TM2ReturnLink.tick code)^[9] empty) := by
  dsimp only
  obtain ⟨used, hu, he, _⟩ := run_packed (fun _ : Fin 1 =>
    (.halt : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool)) 9 empty
  have hc : codeAccesses (fun _ : Fin 1 =>
    (.halt : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool)) = 0 := by decide +kernel
  exact ⟨used, by simpa only [hc, Nat.zero_mul, Nat.add_zero, Nat.mul_one] using hu, he⟩

end ExplainableCrypto.Helios.Computational.TM2TapeRunsControls
