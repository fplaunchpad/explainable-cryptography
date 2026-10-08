import ExplainableCrypto.Helios.Computational.BitTapeInput

/-! Link the executed raw-input conversion to an arbitrary native program,
using the existing return linker and distinct startup/native/halt labels. -/
namespace ExplainableCrypto.Helios.Computational.BitTapeStart
open Turing OracleComp OracleSpec

private def inputLabel {l : Nat} (q : Fin 3) : Fin (l + 4) := ⟨q.val, by have := q.isLt; omega⟩
private def nativeLabel {l : Nat} (q : Fin l) : Fin (l + 4) := ⟨q.val + 4, by omega⟩

/-- Three input phases, a separate halt label, then the original native labels. -/
def program {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) (q : Fin (l + 4)) :
    TM2.Stmt (fun _ : Fin 2 => Bool) (Fin (l + 4)) (Fin 3) :=
  if h : q.val < 3 then
    TM2ReturnLink.redirect inputLabel (nativeLabel entry) (BitTapeInput.program ⟨q.val, h⟩)
  else if h' : q.val < 4 then .halt
  else TM2ReturnLink.redirect nativeLabel 3
    (BitTapeCoverage.program M ⟨q.val - 4, by have := q.isLt; omega⟩)

private theorem input_eq {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) (q : Fin 3) :
    program M entry (inputLabel q) =
      TM2ReturnLink.redirect inputLabel (nativeLabel entry) (BitTapeInput.program q) := by
  fin_cases q <;> simp [program, inputLabel]

private theorem native_eq {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry q : Fin l) : program M entry (nativeLabel q) =
      TM2ReturnLink.redirect nativeLabel 3 (BitTapeCoverage.program M q) := by
  simp [program, nativeLabel]

private theorem stop_eq {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) : program M entry 3 = .halt := by
  simp [program, Nat.mod_eq_of_lt (show 3 < l + 4 by omega)]

def initial {l : Nat} (entry : Fin l) (word : List Bool) : BitOracleMachine.Config 2 (l + 4) 3 :=
  TM2ReturnLink.embed inputLabel (nativeLabel entry) (BitTapeInput.initial word)

/-- Relabel the native result, retaining the full represented tape and head. -/
def result {l : Nat} (c : BitTapeCoverage.Config l) : BitOracleMachine.Config 2 (l + 4) 3 :=
  ⟨c.label.map nativeLabel, BitTapeCoverage.cellCode c.head,
    ![BitTapeCoverage.cells c.before, BitTapeCoverage.cells c.after]⟩

/-- Actual conversion returns to the chosen native entry with the complete
input representation and empty left workspace. -/
theorem convert_run {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) (word : List Bool) :
    ∃ used ≤ 2 * word.length + 3,
      (TM2ReturnLink.tick (program M entry))^[used] (initial entry word) =
        TM2ReturnLink.embed nativeLabel 3
          (BitTapeCoverage.present (BitTapeInput.native (some entry) word)) := by
  obtain ⟨used, hu, he⟩ := TM2ReturnLink.run BitTapeInput.program (program M entry)
    inputLabel (nativeLabel entry) (input_eq M entry) (2 * word.length + 3) (BitTapeInput.initial word)
    (by rw [BitTapeInput.run]; rfl)
  rw [BitTapeInput.run] at he
  exact ⟨used, hu, he⟩

/-- Source linking reaches the actual native result, then halts through its
separate terminal label. The conversion cannot restart on native return. -/
theorem run {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) (word : List Bool) (fuel : Nat)
    (halted : ((BitTapeCoverage.tick M)^[fuel] (BitTapeInput.native (some entry) word)).label = none) :
    ∃ used ≤ 2 * word.length + fuel + 4,
      (TM2ReturnLink.tick (program M entry))^[used] (initial entry word) =
        result ((BitTapeCoverage.tick M)^[fuel] (BitTapeInput.native (some entry) word)) := by
  obtain ⟨before, hb, he⟩ := convert_run M entry word
  obtain ⟨after, ha, hr⟩ := TM2ReturnLink.run (BitTapeCoverage.program M) (program M entry)
    nativeLabel 3 (native_eq M entry) fuel
      (BitTapeCoverage.present (BitTapeInput.native (some entry) word))
      (by rw [BitTapeCoverage.source_run]; exact halted)
  rw [BitTapeCoverage.source_run] at hr
  refine ⟨1 + (after + before), by omega, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, he, hr]
  simp only [Function.iterate_one, TM2ReturnLink.tick, TM2ReturnLink.embed,
    BitTapeCoverage.present, halted, Option.elim_none, TM2.step, stop_eq, TM2.stepAux,
    Option.getD_some, result, Option.map_none]

private theorem redirect_cost {s l r m : Nat} (labels : Fin l → Fin r) (ret : Fin r)
    (q : TM2.Stmt (fun _ : Fin s => Bool) (Fin l) (Fin m)) :
    BitOracleMachine.localCost (TM2ReturnLink.redirect labels ret q) =
      BitOracleMachine.localCost q := by
  induction q <;> simp_all [TM2ReturnLink.redirect, BitOracleMachine.localCost]

/-- The conversion and native code share a fixed source-operation bound. -/
theorem local_cost {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) (q : Fin (l + 4)) : BitOracleMachine.localCost (program M entry q) ≤ 7 := by
  unfold program
  split
  · rw [redirect_cost]
    exact (BitTapeInput.local_cost _).trans (by decide)
  · split
    · change 1 ≤ 7
      omega
    · rw [redirect_cost]
      exact BitTapeCoverage.local_cost M _

/-- Both the observed source duration and its charge are derived from raw
input length and the original native halt bound. -/
theorem charged_run {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) (word : List Bool) (fuel : Nat)
    (halted : ((BitTapeCoverage.tick M)^[fuel] (BitTapeInput.native (some entry) word)).label = none) :
    ∃ used ≤ 2 * word.length + fuel + 4, ∃ charge ≤ 7 * (2 * word.length + fuel + 4),
      BitOracleMachine.run (fun q => .compute (program M entry q)) used (initial entry word) =
        pure (result ((BitTapeCoverage.tick M)^[fuel] (BitTapeInput.native (some entry) word)), charge) := by
  obtain ⟨used, hu, he⟩ := run M entry word fuel halted
  obtain ⟨charge, hc, hr⟩ := BitOracleMachine.compute_run_cost (program M entry) 7
    (local_cost M entry) used (initial entry word)
  rw [he] at hr
  exact ⟨used, hu, charge, hc.trans (Nat.mul_le_mul_left 7 hu), hr⟩

private theorem initial_source {l : Nat} (entry : Fin l) (word : List Bool) :
    initial entry word = BitOracleInitialInput.source 1 (some (inputLabel 0)) 0 word := by
  have hs : Function.update (fun _ : Fin 2 => ([] : List Bool)) 1 word = ![[], word] := by
    funext k; fin_cases k <;> simp [Function.update]
  change (⟨some (inputLabel 0), 0, ![[], word]⟩ : BitOracleMachine.Config 2 (l + 4) 3) =
    ⟨some (inputLabel 0), 0, Function.update (fun _ => []) 1 word⟩
  rw [hs]

private theorem initial_height {l : Nat} (entry : Fin l) (word : List Bool) :
    TM2TapeRuns.height (initial entry word).stk = word.length := by
  change Finset.univ.sup (fun i : Fin 2 => (![[], word] i).length) = word.length
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro i _
    fin_cases i <;> simp
  · exact Finset.le_sup (f := fun i : Fin 2 => (![[], word] i).length) (Finset.mem_univ 1)

/-- From physical raw input to completed native computation, including all
conversion/linking costs. Only the original native halt bound is assumed. -/
theorem physical_run {l : Nat} [NeZero l] (M : TM0.Machine BitTapeCoverage.Cell (Fin l))
    (entry : Fin l) (word : List Bool) (fuel limit : Nat)
    (halted : ((BitTapeCoverage.tick M)^[fuel] (BitTapeInput.native (some entry) word)).label = none) :
    let code : BitOracleMachine.Code 2 (l + 4) 3 := fun q => .compute (program M entry q)
    let bound := 7 * (2 * word.length + fuel + 4)
    let clock := BitOracleTapeCap.unitCost (word.length + bound) * bound *
      BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4 * word.length + 8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 1 (some (inputLabel 0)) 0 (startup + clock)
          (BitOracleInitialInput.initial word)) =
        pure (some (result ((BitTapeCoverage.tick M)^[fuel] (BitTapeInput.native (some entry) word)))) := by
  obtain ⟨used, _, charge, hq, hr⟩ := charged_run M entry word fuel halted
  have hw : BitOracleLoopBounded.Within limit (7 * (2 * word.length + fuel + 4))
      (BitOracleMachine.run (fun q => .compute (program M entry q)) used
        (BitOracleInitialInput.source 1 (some (inputLabel 0)) 0 word)) := by
    rw [← initial_source entry word, hr]
    exact ⟨by simp [result, halted], hq⟩
  obtain ⟨startup, hs, he⟩ := BitOracleInitialInput.run_source_bounded
    (fun q => .compute (program M entry q)) 1 (some (inputLabel 0)) 0 word used limit
    (7 * (2 * word.length + fuel + 4)) hw
  rw [← initial_source entry word, initial_height, hr] at he
  exact ⟨startup, hs, by simpa only [Nat.add_zero, simulateQ_pure, map_pure] using he⟩

end ExplainableCrypto.Helios.Computational.BitTapeStart
