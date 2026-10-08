import ExplainableCrypto.Helios.Computational.BinaryModMultiplyRun
import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded

/-! Loaded-coordinate correspondence and derived physical execution for the
multiplier. Initial parsing and enclosing constructor operand routing remain
separate: these statements start at the specified resident digit layout. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModMultiply
open OracleComp OracleSpec BitOracleMachine

/-- The controller clock is polynomial in modulus width and multiplier length,
including actual complement preparation, input reversal and final cleanup. -/
theorem clock_le_product (p width : Nat) :
    clock p width ≤ 38*(width+1)*(p.size+1) := by
  unfold clock
  nlinarith

/-- Executed multiplication on public residue coordinates implements the
historical group's additive notation. The modulus is p, not scalar order q. -/
theorem group_coordinates {p q : Nat} [NeZero p] (x y : PrimeGroup p q) :
    tick^[clock p (primeGroupCoordinate y).val.bits.length]
      (start (primeGroupCoordinate x).val.bits (primeGroupCoordinate y).val.bits p.bits) =
      result (primeGroupCoordinate (x+y)).val.bits (primeGroupCoordinate x).val.bits p.bits := by
  have h := padded_run p (primeGroupCoordinate x).val (primeGroupCoordinate y).val.bits
    (ZMod.val_lt (primeGroupCoordinate x))
  simpa only [bitsValue_bits,primeGroupCoordinate_add,ZMod.val_mul] using h

/-- The complete loaded multiplier's halt and charge derive the compiler contract. -/
theorem within (p x limit : Nat) (raw : List Bool) (hx : x < p) :
    BitOracleLoopBounded.Within limit (32*clock p raw.length)
      (BitOracleMachine.run code (clock p raw.length) (start x.bits raw p.bits)) := by
  obtain ⟨c,hc,he⟩ := charged p x raw hx
  rw [he]
  exact ⟨rfl,hc⟩

/-- Actual primitive execution from resident digits. Initial height includes
retained x/p and the loaded multiplier; no supplied runtime certificate is used. -/
theorem physical_run (p x limit : Nat) (raw : List Bool) (hx : x < p) :
    let cfg := start x.bits raw p.bits
    let B := 32*clock p raw.length
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code T
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      pure (some (result ((x*bitsValue raw)%p).bits x.bits p.bits)) := by
  dsimp only
  have h := BitOraclePrimitiveBounded.run_source_bounded code (clock p raw.length) limit
    (32*clock p raw.length) (start x.bits raw p.bits) [] (OracleTapeOutput.wordTape [])
    (within p x limit raw hx)
  simp only [List.length_nil,Nat.add_zero] at h
  rw [h]
  obtain ⟨c,_,he⟩ := charged p x raw hx
  rw [he]
  simp

#print axioms clock_le_product
#print axioms group_coordinates
#print axioms within
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.BinaryModMultiply
