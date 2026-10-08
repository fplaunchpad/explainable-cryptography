import ExplainableCrypto.Helios.Computational.TM2TapeRuns
import Mathlib.Tactic.Ring
import ExplainableCrypto.Helios.Computational.BitOraclePortTransfer

/-! Apply the existing tape translation's quantitative bound to the actual
oracle-port programs, including their saved memory and complete caller frame. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleTapeCost
open Turing TM2to1 TM2TapeCost BitOraclePortTransfer

/-- Every actual outgoing-port statement makes at most three stack accesses. -/
theorem request_accesses {s l m : Nat} (port : Fin s) (phase : BitPortTransfer.Label) :
    accesses (requestProgram (l := l) (m := m) port phase) ≤ 3 := by
  cases phase with
  | clear => exact (by decide : 1 ≤ 3)
  | copy phase =>
    cases phase with
    | false => exact (by decide : 2 ≤ 3)
    | true => exact Nat.le_refl 3
  | done => exact Nat.zero_le 3

/-- The consuming response program has the same per-statement access bound. -/
theorem response_accesses {s l m : Nat} (port : Fin s) (phase : BitPortTransfer.Label) :
    accesses (program (l := l) (m := m) port phase) ≤ 3 := by
  cases phase with
  | clear => exact (by decide : 1 ≤ 3)
  | copy phase =>
    cases phase with
    | false => exact (by decide : 2 ≤ 3)
    | true => exact Nat.le_refl 3
  | done => exact (by decide : 1 ≤ 3)

private theorem three_access_step {s l m : Nat}
    (M : BitPortTransfer.Label → TM2.Stmt (fun _ : Ports s => Bool)
      BitPortTransfer.Label ((Fin l × Fin m) × Option Bool))
    (hm : ∀ phase, accesses (M phase) ≤ 3)
    (phase : BitPortTransfer.Label) (v : (Fin l × Fin m) × Option Bool)
    (tapes : Ports s → List Bool) (H : Nat) (hH : ∀ k, (tapes k).length ≤ H)
    (cfg : TM2TapeCost.Config (K := Ports s) (Γ := fun _ => Bool)
      (Λ := BitPortTransfer.Label) (V := (Fin l × Fin m) × Option Bool))
    (hcfg : TrCfg (⟨some phase, v, tapes⟩ : BitOraclePortTransfer.Config s l m) cfg) :
    ∃ used ≤ 6 * H + 25, ∃ out,
      TrCfg (TM2.stepAux (M phase) v tapes) out ∧ (tick M)^[used] cfg = out := by
  obtain ⟨used, hu, out, ho, he⟩ := source_step M phase v tapes H hH cfg hcfg
  have ha := hm phase
  have hw := Nat.mul_le_mul ha (by omega : 2 * (H + accesses (M phase)) + 2 ≤ 2 * (H + 3) + 2)
  unfold work at hu
  exact ⟨used, by omega, out, ho, he⟩

/-- Each actual request-program transition has a derived tape bound, retaining
all caller/private columns through Mathlib's complete translation relation. -/
theorem request_step {s l m : Nat} (port : Fin s)
    (phase : BitPortTransfer.Label) (v : (Fin l × Fin m) × Option Bool)
    (tapes : Ports s → List Bool) (H : Nat) (hH : ∀ k, (tapes k).length ≤ H)
    (cfg : TM2TapeCost.Config (K := Ports s) (Γ := fun _ => Bool)
      (Λ := BitPortTransfer.Label) (V := (Fin l × Fin m) × Option Bool))
    (hcfg : TrCfg (⟨some phase, v, tapes⟩ : BitOraclePortTransfer.Config s l m) cfg) :
    ∃ used ≤ 6 * H + 25, ∃ out,
      TrCfg (TM2.stepAux (requestProgram port phase) v tapes) out ∧
      (tick (requestProgram port))^[used] cfg = out :=
  three_access_step (requestProgram port) (request_accesses port) phase v tapes H hH cfg hcfg

/-- The response-program transition has the same full-frame tape guarantee. -/
theorem response_step {s l m : Nat} (port : Fin s)
    (phase : BitPortTransfer.Label) (v : (Fin l × Fin m) × Option Bool)
    (tapes : Ports s → List Bool) (H : Nat) (hH : ∀ k, (tapes k).length ≤ H)
    (cfg : TM2TapeCost.Config (K := Ports s) (Γ := fun _ => Bool)
      (Λ := BitPortTransfer.Label) (V := (Fin l × Fin m) × Option Bool))
    (hcfg : TrCfg (⟨some phase, v, tapes⟩ : BitOraclePortTransfer.Config s l m) cfg) :
    ∃ used ≤ 6 * H + 25, ∃ out,
      TrCfg (TM2.stepAux (program port phase) v tapes) out ∧
      (tick (program port))^[used] cfg = out :=
  three_access_step (program port) (response_accesses port) phase v tapes H hH cfg hcfg

open TM2TapeRuns

private theorem three_access_run {s l m : Nat}
    (M : BitPortTransfer.Label → TM2.Stmt (fun _ : Ports s => Bool)
      BitPortTransfer.Label ((Fin l × Fin m) × Option Bool))
    (hm : ∀ phase, accesses (M phase) ≤ 3) (fuel : Nat)
    (src : BitOraclePortTransfer.Config s l m) :
    ∃ used ≤ fuel * (6 * height src.stk + 18 * fuel + 7),
      (tick M)^[used] (pack src) = pack ((TM2ReturnLink.tick M)^[fuel] src) := by
  obtain ⟨used, hu, out, ho, ht, _⟩ := TM2TapeRuns.run M 3 hm fuel
    (height src.stk) src (pack src) (pack_related src) (length_le_height src.stk)
  refine ⟨used, ?_, ht.trans (related_unique _ _ _ ho (pack_related _))⟩
  convert hu using 1
  ring

/-- The whole outgoing transfer executes on the existing TM1 tape translation,
with canonical initial/final data and all caller columns retained. -/
theorem request_run {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request : Fin s) (next : Fin l) (oldPort : List Bool) :
    let src := requestStart cfg request next oldPort
    let B := oldPort.length + 2 * (cfg.stk request).length + 4
    ∃ used ≤ B * (6 * height src.stk + 18 * B + 7),
      (tick (requestProgram request))^[used] (pack src) =
        pack {requestStart cfg request next (cfg.stk request) with l := none} := by
  dsimp only
  obtain ⟨fuel, hf, he⟩ := request_state cfg request next oldPort
  obtain ⟨used, hu, ht⟩ := three_access_run (requestProgram request)
    (request_accesses request) fuel (requestStart cfg request next oldPort)
  refine ⟨used, hu.trans (Nat.mul_le_mul hf (by omega)), ?_⟩
  rw [he] at ht
  exact ht

/-- The whole response transfer has a derived tape bound and returns the actual
resumed caller, with both private columns empty. -/
theorem response_run {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) (answer : List Bool) :
    let src := start cfg destination next answer
    let B := (cfg.stk destination).length + 3 * answer.length + 4
    ∃ used ≤ B * (6 * height src.stk + 18 * B + 7),
      ∃ out : BitOraclePortTransfer.Config s l m,
        (tick (program destination))^[used] (pack src) = pack out ∧
        out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] := by
  dsimp only
  obtain ⟨fuel, hf, hr⟩ := run_resume cfg destination next answer
  obtain ⟨used, hu, ht⟩ := three_access_run (program destination)
    (response_accesses destination) fuel (start cfg destination next answer)
  exact ⟨used, hu.trans (Nat.mul_le_mul hf (by omega)), _, ht, hr⟩

end ExplainableCrypto.Helios.Computational.BitOracleTapeCost
