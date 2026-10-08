import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveStep
import VCVio.OracleComp.EvalDist

/-! Derive the successor-closed control support and fixed global multiplier
for primitive refinement of the reachable historical raw oracle machine. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
open Turing OracleComp OracleSpec BitOraclePortTransfer

/-- Only deterministic residual labels require a support invariant. The
remaining phases store finite tags, finite memory and the unchanged tapes. -/
def Supported {s l m : Nat} (code : BitOracleMachine.Code s l m) : BitOracleTapeLoop.State s l m → Prop
  | .compute source cfg _ _ => cfg.l ∈ Finset.insertNone
      (TM2to1.trSupp (BitOracleTapeLoop.localProgram code source) Finset.univ)
  | .prepare request _ cfg _ _ => cfg.l ∈ Finset.insertNone
      (TM2to1.trSupp (requestProgram request) Finset.univ)
  | .call _ (.response destination cfg _ _) => cfg.l ∈ Finset.insertNone
      (TM2to1.trSupp (program destination) Finset.univ)
  | _ => True

/-- One fixed bound covers finite source labels and every request/response
port. It is independent of tape contents, oracle answers and source fuel. -/
noncomputable def globalFactor {s l m : Nat} (code : BitOracleMachine.Code s l m) : Nat :=
  1 + Finset.univ.sup (fun source => BitOraclePrimitiveCost.factor (BitOracleTapeLoop.localProgram code source)) +
    Finset.univ.sup (fun request : Fin s => BitOraclePrimitiveCost.factor (requestProgram (l := l) (m := m) request)) +
    Finset.univ.sup (fun destination : Fin s => BitOraclePrimitiveCost.factor (program (l := l) (m := m) destination))

private theorem normal_supported {K L V : Type} {Γ : K → Type} [DecidableEq K] [Fintype L]
    (M : L → TM2.Stmt Γ L V) (label : L) :
    some (TM2to1.Λ'.normal label) ∈ Finset.insertNone (TM2to1.trSupp M Finset.univ) := by
  classical
  apply Finset.some_mem_insertNone.mpr
  exact Finset.mem_biUnion.mpr ⟨label, Finset.mem_univ _, Finset.mem_insert_self _ _⟩

private theorem tick_supported {K L V : Type} {Γ : K → Type} [DecidableEq K] [Fintype L] [Inhabited L]
    (M : L → TM2.Stmt Γ L V) (cfg : TM2TapeCost.Config (K := K) (Γ := Γ) (Λ := L) (V := V))
    (h : cfg.l ∈ Finset.insertNone (TM2to1.trSupp M Finset.univ)) :
    (TM2TapeCost.tick M cfg).l ∈ Finset.insertNone (TM2to1.trSupp M Finset.univ) := by
  have hs := BitOraclePrimitiveCost.tape_support M
  cases he : TM1.step (TM2to1.tr M) cfg with
  | none => simpa [TM2TapeCost.tick, he] using h
  | some out =>
    simpa only [TM2TapeCost.tick, he, Option.getD_some] using TM1.step_supports _ hs he h

/-- Initial ready states require no caller-supplied presentation or support. -/
theorem ready_supported {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (label : Option (Fin l)) (memory : Fin m) (tapes : OracleTapeDispatch.Tapes (Ports s)) :
    Supported code (.ready label memory tapes) := trivial

/-- Every successor, for every raw native answer, retains the code-derived
support. Oracle answer width and contents are unrestricted in this invariant. -/
theorem step_supported {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleTapeLoop.State s l m) (h : Supported code cfg) :
    ∀ out ∈ support (BitOracleTapeLoop.step code cfg), Supported code out := by
  let _ : Inhabited BitPortTransfer.Label := ⟨.clear⟩
  cases cfg with
  | ready label memory tapes =>
    cases label with
    | none => simp [BitOracleTapeLoop.step, Supported]
    | some source => cases hc : code source with
      | compute q => simpa [BitOracleTapeLoop.step, hc, Supported] using
          normal_supported (BitOracleTapeLoop.localProgram code source) ()
      | coin destination next => simp [BitOracleTapeLoop.step, hc, Supported]
      | hash request destination next =>
        simpa [BitOracleTapeLoop.step, hc, Supported] using
          (normal_supported (requestProgram (l := l) (m := m) request) BitPortTransfer.Label.clear)
  | compute source cfg query answer =>
    by_cases he : cfg.l.isNone = true
    · simp [BitOracleTapeLoop.step, he, Supported]
    · simpa [BitOracleTapeLoop.step, he, Supported] using
        tick_supported (BitOracleTapeLoop.localProgram code source) cfg h
  | prepare request destination cfg query answer =>
    by_cases he : cfg.l.isNone = true
    · simp [BitOracleTapeLoop.step, he, Supported]
    · simpa [BitOracleTapeLoop.step, he, Supported] using tick_supported (requestProgram request) cfg h
  | call kind cfg => cases cfg with
    | output destination saved cfg answer =>
      by_cases he : cfg.phase = .done <;>
        simp [BitOracleTapeLoop.step, BitOracleTapeCall.step, he, Supported]
    | issue destination saved tapes =>
      simp [BitOracleTapeLoop.step, BitOracleTapeCall.step, support_map, Supported]
    | input destination saved query cfg =>
      by_cases he : cfg.phase = .done
      · simpa [BitOracleTapeLoop.step, BitOracleTapeCall.step, he, Supported] using
          normal_supported (program (l := l) (m := m) destination) BitPortTransfer.Label.clear
      · simp [BitOracleTapeLoop.step, BitOracleTapeCall.step, he, Supported]
    | response destination cfg query answer =>
      by_cases he : cfg.l.isNone = true
      · simp [BitOracleTapeLoop.step, BitOracleTapeCall.step, he, Supported]
      · simpa [BitOracleTapeLoop.step, BitOracleTapeCall.step, he, Supported] using
          tick_supported (program destination) cfg h
    | done cfg query answer => simp [BitOracleTapeLoop.step, Supported]

/-- All states reachable in any finite old-loop execution satisfy the support
invariant, including successors through internal computation and native events. -/
theorem run_supported {s l m : Nat} (code : BitOracleMachine.Code s l m) (fuel : Nat)
    (cfg : BitOracleTapeLoop.State s l m) (h : Supported code cfg) :
    ∀ out ∈ support (BitOracleTapeLoop.run code fuel cfg), Supported code out := by
  induction fuel generalizing cfg with
  | zero => simpa [BitOracleTapeLoop.run] using h
  | succ fuel ih =>
    intro out ho
    obtain ⟨next, hn, hr⟩ := OracleComp.mem_support_bind_peel _ _ ho
    exact ih next (step_supported code cfg h next hn) out hr

private theorem allowance_le {K L V : Type} {Γ : K → Type} [DecidableEq K] [Fintype L]
    (M : L → TM2.Stmt Γ L V) (label : TM2to1.Λ' K Γ L V)
    (h : some label ∈ Finset.insertNone (TM2to1.trSupp M Finset.univ)) :
    TM1PrimitiveCost.allowance (TM2to1.tr M label) ≤ BitOraclePrimitiveCost.factor M :=
  Finset.le_sup (f := fun label => TM1PrimitiveCost.allowance (TM2to1.tr M label))
    (Finset.some_mem_insertNone.mp h)

/-- The local primitive execution allowance is uniformly bounded on all
reachable supported states by the fixed source program's global factor. -/
theorem stepAllowance_le {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleTapeLoop.State s l m) (h : Supported code cfg) :
    stepAllowance code cfg ≤ globalFactor code := by
  have hc (source : Fin l) : BitOraclePrimitiveCost.factor (BitOracleTapeLoop.localProgram code source) ≤
      Finset.univ.sup (fun source => BitOraclePrimitiveCost.factor (BitOracleTapeLoop.localProgram code source)) :=
    Finset.le_sup (f := fun source => BitOraclePrimitiveCost.factor (BitOracleTapeLoop.localProgram code source)) (Finset.mem_univ _)
  have hr (request : Fin s) : BitOraclePrimitiveCost.factor (requestProgram (l := l) (m := m) request) ≤
      Finset.univ.sup (fun request : Fin s => BitOraclePrimitiveCost.factor (requestProgram (l := l) (m := m) request)) :=
    Finset.le_sup (f := fun request : Fin s => BitOraclePrimitiveCost.factor (requestProgram (l := l) (m := m) request)) (Finset.mem_univ _)
  have ha (destination : Fin s) : BitOraclePrimitiveCost.factor (program (l := l) (m := m) destination) ≤
      Finset.univ.sup (fun destination : Fin s => BitOraclePrimitiveCost.factor (program (l := l) (m := m) destination)) :=
    Finset.le_sup (f := fun destination : Fin s => BitOraclePrimitiveCost.factor (program (l := l) (m := m) destination)) (Finset.mem_univ _)
  have one : 1 ≤ globalFactor code := by unfold globalFactor; omega
  cases cfg with
  | ready => exact one
  | compute source cfg query answer =>
    cases he : cfg.l with
    | none => simpa [stepAllowance, he] using one
    | some label =>
      have hh := allowance_le (BitOracleTapeLoop.localProgram code source) label (he ▸ h)
      have := hc source
      simp only [stepAllowance, he]
      unfold globalFactor
      omega
  | prepare request destination cfg query answer =>
    cases he : cfg.l with
    | none => simpa [stepAllowance, he] using one
    | some label =>
      have hh := allowance_le (requestProgram request) label (he ▸ h)
      have := hr request
      simp only [stepAllowance, he]
      unfold globalFactor
      omega
  | call kind cfg => cases cfg with
    | output | issue | input => exact one
    | done => exact Nat.zero_le _
    | response destination cfg query answer =>
      cases he : cfg.l with
      | none => simpa [stepAllowance, he] using one
      | some label =>
        have hh := allowance_le (program destination) label (he ▸ h)
        have := ha destination
        simp only [stepAllowance, he]
        unfold globalFactor
        omega

/-- Every reachable supported old-loop action has bounded primitive matching,
with the actual native query tree and full lowered state in the conclusion. -/
theorem supported_step_match {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : BitOracleTapeLoop.State s l m) (h : Supported code cfg) :
    ∃ used ≤ globalFactor code,
      run code used (lower code cfg) = lower code <$> BitOracleTapeLoop.step code cfg := by
  obtain ⟨used, hu, he⟩ := step_match code cfg
  exact ⟨used, hu.trans (stepAllowance_le code cfg h), he⟩

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveLoop
