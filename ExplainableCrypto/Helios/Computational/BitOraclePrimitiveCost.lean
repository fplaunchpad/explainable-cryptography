import ExplainableCrypto.Helios.Computational.TM1PrimitiveCost
import ExplainableCrypto.Helios.Computational.BitOracleTapeCompute
import ExplainableCrypto.Helios.Computational.BitOracleTapeCost

/-! Primitive costs for the actual deterministic regions of the oracle tape loop.
Finite support comes from the pinned compilers and finite source labels. This
module does not yet assemble a primitive open-oracle loop or load initial input. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCost
open Turing TM2TapeRuns BitOraclePortTransfer

section Translation
variable {K Λ V : Type} {Γ : K → Type} [DecidableEq K] [Fintype Λ]

omit [DecidableEq K] in
private theorem supportsStmt (q : TM2.Stmt Γ Λ V) : TM2.SupportsStmt Finset.univ q := by
  induction q with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ ha hb => exact ⟨ha, hb⟩
  | goto => exact fun _ => Finset.mem_univ _
  | halt => trivial

/-- Fixed code determines a finite per-TM1-tick multiplier. -/
noncomputable def factor (M : Λ → TM2.Stmt Γ Λ V) : Nat :=
  TM1PrimitiveCost.multiplier (TM2to1.tr M) (TM2to1.trSupp M Finset.univ)

variable [Inhabited Λ] [Inhabited V]

omit [Inhabited V] [DecidableEq K] in
private theorem source_support (M : Λ → TM2.Stmt Γ Λ V) :
    TM2.Supports M Finset.univ := ⟨Finset.mem_univ _, fun label _ => supportsStmt (M label)⟩

omit [Inhabited V] in
/-- The actual stack-to-tape compiler has derived finite support. -/
theorem tape_support (M : Λ → TM2.Stmt Γ Λ V) :
    TM1.Supports (TM2to1.tr M) (TM2to1.trSupp M Finset.univ) :=
  TM2to1.tr_supports M (source_support M)

/-- Both existing translations have a derived finite successor-closed control
support. Finiteness is of the reachable program, not the ambient statement type. -/
theorem finite_support [Fintype V] (M : Λ → TM2.Stmt Γ Λ V) :
    TM0.Supports (TM1to0.tr (TM2to1.tr M))
      ↑(TM1to0.trStmts (TM2to1.tr M) (TM2to1.trSupp M Finset.univ)) :=
  TM1to0.tr_supports _ (TM2to1.tr_supports _ (source_support M))

/-- Starting with any canonical source configuration, finite support and the
primitive multiplier are derived, without a caller support certificate. -/
theorem run_packed [Fintype K] (M : Λ → TM2.Stmt Γ Λ V) (fuel : Nat) (cfg : TM2.Cfg Γ Λ V) :
    ∃ used ≤ fuel * factor M,
      (TM1PrimitiveCost.tick (TM2to1.tr M))^[used]
        (TM1to0.trCfg (TM2to1.tr M) (pack cfg)) =
      TM1to0.trCfg (TM2to1.tr M) ((TM2TapeCost.tick M)^[fuel] (pack cfg)) := by
  have hc : (pack cfg).l ∈ Finset.insertNone (TM2to1.trSupp M Finset.univ) := by
    classical
    cases h : cfg.l with
    | none => simp [pack, h]
    | some label =>
      simp only [pack, h, Option.map_some, Finset.some_mem_insertNone]
      exact Finset.mem_biUnion.mpr ⟨label, Finset.mem_univ _, Finset.mem_insert_self _ _⟩
  exact TM1PrimitiveCost.run _ _ (TM2to1.tr_supports _ (source_support M)) fuel (pack cfg) hc

end Translation

/-- The actual returning computation executes through both pinned compilers,
with exact complete output and a constant depending only on its fixed code. -/
theorem compute_run {s l m : Nat}
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m))
    (cfg : BitOracleMachine.Config s l m) :
    let _ : Inhabited (Option (Fin l) × Fin m) := ⟨(cfg.l, cfg.var)⟩
    let M := fun _ : Unit => BitOracleTapeCompute.compile q
    let a := TM2TapeCost.accesses q
    let H := height (BitOracleTapeCompute.framed cfg).stk
    ∃ used ≤ (1 + a * (2 * (H + a) + 2)) * factor M,
      (TM1PrimitiveCost.tick (TM2to1.tr M))^[used]
        (TM1to0.trCfg (TM2to1.tr M) (pack (BitOracleTapeCompute.entry cfg))) =
      TM1to0.trCfg (TM2to1.tr M)
        (pack (BitOracleTapeCompute.result (TM2.stepAux q cfg.var cfg.stk))) := by
  dsimp only
  let _ : Inhabited (Option (Fin l) × Fin m) := ⟨(cfg.l, cfg.var)⟩
  obtain ⟨fuel, hf, he⟩ := BitOracleTapeCompute.run q cfg
  obtain ⟨used, hu, ht⟩ := run_packed (fun _ : Unit => BitOracleTapeCompute.compile q)
    fuel (BitOracleTapeCompute.entry cfg)
  exact ⟨used, hu.trans (Nat.mul_le_mul_right _ hf), by rw [he] at ht; exact ht⟩

/-- The actual outgoing transfer has a derived primitive bound and canonical
full output, including the saved caller context and untouched original words. -/
theorem request_run {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request : Fin s) (next : Fin l) (oldPort : List Bool) :
    let _ : Inhabited BitPortTransfer.Label := ⟨.clear⟩
    let _ : Inhabited ((Fin l × Fin m) × Option Bool) := ⟨((next, cfg.var), none)⟩
    let M := requestProgram (l := l) (m := m) request
    let src := requestStart cfg request next oldPort
    let B := oldPort.length + 2 * (cfg.stk request).length + 4
    ∃ used ≤ (B * (6 * height src.stk + 18 * B + 7)) * factor M,
      (TM1PrimitiveCost.tick (TM2to1.tr M))^[used]
        (TM1to0.trCfg (TM2to1.tr M) (pack src)) =
      TM1to0.trCfg (TM2to1.tr M)
        (pack {requestStart cfg request next (cfg.stk request) with l := none}) := by
  dsimp only
  let _ : Inhabited BitPortTransfer.Label := ⟨.clear⟩
  let _ : Inhabited ((Fin l × Fin m) × Option Bool) := ⟨((next, cfg.var), none)⟩
  obtain ⟨fuel, hf, he⟩ := BitOracleTapeCost.request_run cfg request next oldPort
  obtain ⟨used, hu, ht⟩ := run_packed (requestProgram request) fuel (requestStart cfg request next oldPort)
  exact ⟨used, hu.trans (Nat.mul_le_mul_right _ hf), by rw [he] at ht; exact ht⟩

/-- The actual response consumes its private answer and restores the complete
caller with both private columns empty, now with a primitive execution bound. -/
theorem response_run {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) (answer : List Bool) :
    let _ : Inhabited BitPortTransfer.Label := ⟨.clear⟩
    let _ : Inhabited ((Fin l × Fin m) × Option Bool) := ⟨((next, cfg.var), none)⟩
    let M := program (l := l) (m := m) destination
    let src := start cfg destination next answer
    let B := (cfg.stk destination).length + 3 * answer.length + 4
    ∃ used ≤ (B * (6 * height src.stk + 18 * B + 7)) * factor M,
      ∃ out : BitOraclePortTransfer.Config s l m,
        (TM1PrimitiveCost.tick (TM2to1.tr M))^[used]
          (TM1to0.trCfg (TM2to1.tr M) (pack src)) = TM1to0.trCfg (TM2to1.tr M) (pack out) ∧
        out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] := by
  dsimp only
  let _ : Inhabited BitPortTransfer.Label := ⟨.clear⟩
  let _ : Inhabited ((Fin l × Fin m) × Option Bool) := ⟨((next, cfg.var), none)⟩
  obtain ⟨fuel, hf, out, he, ho⟩ := BitOracleTapeCost.response_run cfg destination next answer
  obtain ⟨used, hu, ht⟩ := run_packed (program destination) fuel (start cfg destination next answer)
  exact ⟨used, hu.trans (Nat.mul_le_mul_right _ hf), out, by rw [he] at ht; exact ht, ho⟩

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCost
