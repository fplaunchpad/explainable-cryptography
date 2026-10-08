import ExplainableCrypto.Helios.Computational.BinaryModPowerRun
import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded

/-! The loaded power controller implements public-coordinate scalar action.
The source theorem retains the original exponent for the second encryption
coordinate. Public-record parsing and actual constructor routing remain separate. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModPower
open OracleComp OracleSpec BitOracleMachine

theorem clock_le_product (p width : Nat) :
    clock p width ≤ 80*(width+1)*(p.size+1)^2 := by
  unfold clock BinaryModMultiply.clock
  nlinarith [sq_nonneg (p.size : Int)]

private theorem value_pow {p : Nat} [NeZero p] (a : ZMod p) (n : Nat) :
    (a^n).val = a.val^n%p := by
  induction n with
  | zero => simp only [pow_zero,ZMod.val_one_eq_one_mod]
  | succ n ih => rw [pow_succ,ZMod.val_mul,ih,Nat.pow_succ,Nat.mod_mul_mod]

/-- The original scalar action is public modular exponentiation. The historical
prime modulus derives the controller's nontrivial-modulus initialization premise. -/
theorem group_coordinates {p q : Nat} [Fact p.Prime] [NeZero q]
    (r : ZMod q) (x : PrimeGroup p q) (context : List Bool) :
    tick^[clock p r.val.bits.length]
      (start (primeGroupCoordinate x).val.bits r.val.bits p.bits context) =
      result (primeGroupCoordinate (r • x)).val.bits
        (primeGroupCoordinate x).val.bits r.val.bits p.bits context := by
  have h := padded_run p (primeGroupCoordinate x).val r.val.bits context
    (Fact.out : p.Prime).two_le (ZMod.val_lt (primeGroupCoordinate x))
  simpa only [bitsValue_bits,primeGroupCoordinate_smul,value_pow] using h

/-- The full loaded power run discharges the primitive compiler contract. -/
theorem within (p base limit : Nat) (raw context : List Bool)
    (hp : 2 ≤ p) (hb : base < p) :
    BitOracleLoopBounded.Within limit (32*clock p raw.length)
      (BitOracleMachine.run code (clock p raw.length) (start base.bits raw p.bits context)) := by
  obtain ⟨c,hc,he⟩ := charged p base raw context hp hb
  rw [he]
  exact ⟨rfl,hc⟩

/-- Actual primitive execution from the lowered ready state. Its height includes
original exponent and opaque context, with initially empty auxiliary oracle tapes. -/
theorem physical_run (p base limit : Nat) (raw context : List Bool)
    (hp : 2 ≤ p) (hb : base < p) :
    let cfg := start base.bits raw p.bits context
    let B := 32*clock p raw.length
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code T
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      pure (some (result (base^bitsValue raw%p).bits base.bits raw p.bits context)) := by
  dsimp only
  have h := BitOraclePrimitiveBounded.run_source_bounded code (clock p raw.length) limit
    (32*clock p raw.length) (start base.bits raw p.bits context) [] (OracleTapeOutput.wordTape [])
    (within p base limit raw context hp hb)
  simp only [List.length_nil,Nat.add_zero] at h
  rw [h]
  obtain ⟨c,_,he⟩ := charged p base raw context hp hb
  rw [he]
  simp

#print axioms clock_le_product
#print axioms group_coordinates
#print axioms within
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.BinaryModPower
