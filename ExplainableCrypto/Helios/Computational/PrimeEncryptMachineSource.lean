import ExplainableCrypto.Helios.Computational.PrimeEncryptMachineRun
import ExplainableCrypto.Helios.Computational.PrimeGroup
import ExplainableCrypto.Helios.Computational.HonestBallot
import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded

/-! The loaded two-power controller executes the actual historical encryptWith
coordinates. Public-record parsing and nonce-prefix routing from the preceding
sampler remain distinct caller obligations. -/
namespace ExplainableCrypto.Helios.Computational.PrimeEncryptMachine
open OracleComp OracleSpec BitOracleMachine

theorem clock_le_product (p width : Nat) :
    clock p width ≤ 220*(width+1)*(p.size+1)^2 := by
  unfold clock BinaryModPower.clock BinaryModMultiply.clock
  nlinarith [sq_nonneg (p.size : Int)]

private theorem value_pow {p : Nat} [NeZero p] (a : ZMod p) (n : Nat) :
    (a^n).val = a.val^n%p := by
  simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using (ZMod.val_natCast p (a.val^n))

/-- Numeric coordinates of the original encryption, shared by repeated resident requests. -/
theorem coordinate_values {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (r : ZMod q) (vote : Bool) :
    ((primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).1).val,
      (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).2).val) =
    ((primeGroupCoordinate g).val^r.val%p,
      ((primeGroupCoordinate pk).val^r.val%p)*
        (if vote then (primeGroupCoordinate g).val else 1)%p) := by
  have hs := primeGroup_encrypt_coordinates g pk r (voteScalar vote)
  have hn := congrArg (fun pair : ZMod p × ZMod p => (pair.1.val,pair.2.val)) hs
  rw [hn]
  simp only [value_pow,ZMod.val_mul]
  cases vote
  · simp [voteScalar,ZMod.val_zero]
  · have hq : 1 < q := (Fact.out : q.Prime).one_lt
    have ho : (1 : ZMod q).val = 1 := by rw [ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt hq]
    simp [voteScalar,ho,Nat.mod_eq_of_lt (ZMod.val_lt (primeGroupCoordinate g)),Nat.mul_comm]

/-- Actual encryptWith, both coordinates, with retained original inputs and
complete workspace cleanup. Prime p derives the power initialization premise. -/
theorem source {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (r : ZMod q) (vote : Bool) (context : List Bool) :
    tick^[clock p r.val.bits.length]
      (start (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits
        r.val.bits p.bits context vote) =
      result (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).1).val.bits
        (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).2).val.bits
        (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits
        r.val.bits p.bits context vote := by
  have h := padded_run p (primeGroupCoordinate g).val (primeGroupCoordinate pk).val
    r.val.bits vote context (Fact.out : p.Prime).two_le
    (ZMod.val_lt (primeGroupCoordinate g)) (ZMod.val_lt (primeGroupCoordinate pk))
  have ha := congrArg Prod.fst (coordinate_values g pk r vote)
  have hb := congrArg Prod.snd (coordinate_values g pk r vote)
  dsimp only at ha hb
  rw [ha,hb]
  simpa only [bitsValue_bits] using h

theorem within (p g pk limit : Nat) (raw : List Bool) (vote : Bool) (context : List Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    BitOracleLoopBounded.Within limit (32*clock p raw.length)
      (BitOracleMachine.run code (clock p raw.length) (start g.bits pk.bits raw p.bits context vote)) := by
  obtain ⟨c,hc,he⟩ := charged p g pk raw vote context hp hg hpk
  rw [he]
  exact ⟨rfl,hc⟩

/-- Physical execution from the lowered resident ready state and empty auxiliary
oracle tapes. The actual height includes public inputs, nonce, vote and context. -/
theorem physical_run (p g pk limit : Nat) (raw : List Bool) (vote : Bool) (context : List Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    let cfg := start g.bits pk.bits raw p.bits context vote
    let B := 32*clock p raw.length
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code T
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      pure (some (result (g^bitsValue raw%p).bits
        (((pk^bitsValue raw%p)*(if vote then g else 1))%p).bits g.bits pk.bits raw p.bits context vote)) := by
  dsimp only
  have h := BitOraclePrimitiveBounded.run_source_bounded code (clock p raw.length) limit
    (32*clock p raw.length) (start g.bits pk.bits raw p.bits context vote) [] (OracleTapeOutput.wordTape [])
    (within p g pk limit raw vote context hp hg hpk)
  simp only [List.length_nil,Nat.add_zero] at h
  rw [h]
  obtain ⟨c,_,he⟩ := charged p g pk raw vote context hp hg hpk
  rw [he]
  simp

#print axioms clock_le_product
#print axioms source
#print axioms within
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.PrimeEncryptMachine

#print axioms ExplainableCrypto.Helios.Computational.PrimeEncryptMachine.coordinate_values
