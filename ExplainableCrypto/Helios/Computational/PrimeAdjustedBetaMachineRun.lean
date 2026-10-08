import ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame

/-! Actual adjusted-beta construction by two existing arithmetic calls. Fixed
frame relocations use resident g, beta, p and q-1 digits without copies. Every
operand presentation, return, final empty work port and charge is derived here.
The typed subgroup interpretation belongs to the enclosing source theorem. -/

namespace ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 65536

/-- The actual power call preserves its framed instruction tree and live return. -/
theorem power_code (l : Fin 192) : code (powerLabel l) =
    BitOracleReturnLink.command powerLabel (some 1)
      ((BitOracleStackFrame.code powerLayout BinaryModPower.code) l) := by
  fin_cases l <;> rfl

/-- The actual product call retains its successful halt after label relocation. -/
theorem multiply_code (l : Fin 86) : code (multiplyLabel l) =
    BitOracleReturnLink.command multiplyLabel none
      ((BitOracleStackFrame.code multiplyLayout BinaryModMultiply.code) l) := by
  fin_cases l <;> rfl

theorem local_cost (l : Fin size) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

#print axioms power_code
#print axioms multiply_code
#print axioms local_cost
end ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine

namespace ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

private def readyPower (old : Fin 39 → List Bool) : Config :=
  ⟨some (powerLabel (BinaryModPower.copyLabel 0 0)),0,initialWords old⟩
private def powerWords (old : Fin 39 → List Bool) (inverse : List Bool) :=
  Function.update (initialWords old) 23 inverse
private def returnedPower (old : Fin 39 → List Bool) (inverse : List Bool) : Config :=
  ⟨some 1,2,powerWords old inverse⟩
private def readyMultiply (old : Fin 39 → List Bool) (inverse : List Bool) : Config :=
  ⟨some (multiplyLabel (BinaryModMultiply.copyLabel 0)),0,powerWords old inverse⟩
private def powerFrame (old : Fin 39 → List Bool) : Fin 25 → List Bool :=
  fun k => initialWords old (powerLayout (.inr k))
private def multiplyFrame (old : Fin 39 → List Bool) (inverse : List Bool) : Fin 29 → List Bool :=
  fun k => powerWords old inverse (multiplyLayout (.inr k))

private theorem entry_step (old : Fin 39 → List Bool) :
    BitOracleMachine.step code (start old) = pure (readyPower old,3) := rfl
private theorem middle_step (old : Fin 39 → List Bool) (inverse : List Bool) :
    BitOracleMachine.step code (returnedPower old inverse) = pure (readyMultiply old inverse,3) := rfl

private theorem power_input (p q g beta : Nat) (frame : Fin 20 → List Bool) :
    BitOracleReturnLink.embed powerLabel (some 1)
      (BitOracleStackFrame.embed powerLayout
        (BinaryModPower.start g.bits (q-1).bits p.bits (frame 12))
        (powerFrame (inputWords p q g beta frame))) =
      readyPower (inputWords p q g beta frame) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem power_output (p q g beta : Nat) (frame : Fin 20 → List Bool)
    (inverse : List Bool) :
    BitOracleReturnLink.embed powerLabel (some 1)
      (BitOracleStackFrame.embed powerLayout
        (BinaryModPower.result inverse g.bits (q-1).bits p.bits (frame 12))
        (powerFrame (inputWords p q g beta frame))) =
      returnedPower (inputWords p q g beta frame) inverse := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem multiply_input (p q g beta : Nat) (frame : Fin 20 → List Bool)
    (inverse : List Bool) :
    BitOracleReturnLink.embed multiplyLabel none
      (BitOracleStackFrame.embed multiplyLayout
        (BinaryModMultiply.start beta.bits inverse p.bits)
        (multiplyFrame (inputWords p q g beta frame) inverse)) =
      readyMultiply (inputWords p q g beta frame) inverse := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem multiply_output (p q g beta : Nat) (frame : Fin 20 → List Bool)
    (inverse answer : List Bool) :
    BitOracleReturnLink.embed multiplyLabel none
      (BitOracleStackFrame.embed multiplyLayout
        (BinaryModMultiply.result answer beta.bits p.bits)
        (multiplyFrame (inputWords p q g beta frame) inverse)) =
      result answer (inputWords p q g beta frame) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Uniform product width is derived from the actual reduced inverse digits. -/
private theorem multiply_wide (p beta inverse : Nat) (hb : beta < p) (hi : inverse < p) :
    ∃ charge ≤ 32*BinaryModMultiply.clock p p.size,
      BitOracleMachine.run BinaryModMultiply.code (BinaryModMultiply.clock p p.size)
        (BinaryModMultiply.start beta.bits inverse.bits p.bits) =
      pure (BinaryModMultiply.result ((beta*inverse)%p).bits beta.bits p.bits,charge) := by
  have hw : inverse.bits.length ≤ p.size := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size hi.le
  have hclock : BinaryModMultiply.clock p inverse.bits.length ≤ BinaryModMultiply.clock p p.size := by
    unfold BinaryModMultiply.clock
    gcongr
  have he := BinaryModMultiply.padded_run p beta inverse.bits hb
  rw [bitsValue_bits] at he
  obtain ⟨extra,hclock⟩ := Nat.exists_eq_add_of_le hclock
  have hfull : BinaryModMultiply.tick^[BinaryModMultiply.clock p p.size]
      (BinaryModMultiply.start beta.bits inverse.bits p.bits) =
      BinaryModMultiply.result ((beta*inverse)%p).bits beta.bits p.bits := by
    rw [hclock,Nat.add_comm _ extra,Function.iterate_add_apply,he]
    exact Function.iterate_fixed (by rfl) extra
  obtain ⟨charge,hc,hr⟩ := BitOracleMachine.compute_run_cost BinaryModMultiply.program 32
    BinaryModMultiply.local_cost (BinaryModMultiply.clock p p.size)
      (BinaryModMultiply.start beta.bits inverse.bits p.bits)
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run BinaryModMultiply.code (BinaryModMultiply.clock p p.size)
      (BinaryModMultiply.start beta.bits inverse.bits p.bits) =
    pure (BinaryModMultiply.tick^[BinaryModMultiply.clock p p.size]
      (BinaryModMultiply.start beta.bits inverse.bits p.bits),charge) at hr
  rw [hr,hfull]

#print axioms power_input
#print axioms power_output
#print axioms multiply_input
#print axioms multiply_output
#print axioms multiply_wide
end ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine

namespace ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run

private theorem multiply_charged (p q g beta inverse : Nat) (frame : Fin 20 → List Bool)
    (hb : beta < p) (hi : inverse < p) :
    ∃ charge ≤ 32*BinaryModMultiply.clock p p.size,
      BitOracleMachine.run code (BinaryModMultiply.clock p p.size)
        (readyMultiply (inputWords p q g beta frame) inverse.bits) =
      pure (result ((beta*inverse)%p).bits (inputWords p q g beta frame),charge) := by
  obtain ⟨charge,hc,he⟩ := multiply_wide p beta inverse hb hi
  have hf := BitOracleStackFrame.run multiplyLayout BinaryModMultiply.code
    (BinaryModMultiply.clock p p.size) (BinaryModMultiply.start beta.bits inverse.bits p.bits)
    (multiplyFrame (inputWords p q g beta frame) inverse.bits)
  rw [he,map_pure] at hf
  have hr := BitOracleReturnLink.rename_run
    (BitOracleStackFrame.code multiplyLayout BinaryModMultiply.code) code multiplyLabel
    multiply_code (BinaryModMultiply.clock p p.size)
    (BitOracleStackFrame.embed multiplyLayout (BinaryModMultiply.start beta.bits inverse.bits p.bits)
      (multiplyFrame (inputWords p q g beta frame) inverse.bits))
  rw [hf,map_pure,multiply_input,multiply_output] at hr
  exact ⟨charge,hc,hr⟩

private theorem tail_charged (p q g beta inverse : Nat) (frame : Fin 20 → List Bool)
    (hb : beta < p) (hi : inverse < p) :
    ∃ charge ≤ 32*BinaryModMultiply.clock p p.size+3,
      BitOracleMachine.run code (BinaryModMultiply.clock p p.size+1)
        (returnedPower (inputWords p q g beta frame) inverse.bits) =
      pure (result ((beta*inverse)%p).bits (inputWords p q g beta frame),charge) := by
  obtain ⟨charge,hc,he⟩ := multiply_charged p q g beta inverse frame hb hi
  refine ⟨3+charge,by omega,?_⟩
  rw [BitOracleMachine.run,middle_step,pure_bind,he,pure_bind]

/-- Both existing arithmetic executions, both actual guards and every retained
word compose without copying or caller-supplied runtime premises. -/
theorem charged (p q g beta : Nat) (hp : 2 ≤ p) (hg : g < p) (hb : beta < p)
    (frame : Fin 20 → List Bool) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q) (start (inputWords p q g beta frame)) =
      pure (result (answer p q g beta).bits (inputWords p q g beta frame),charge) := by
  have hclock : clock p q =
      (BinaryModPower.clock p (q-1).size+(BinaryModMultiply.clock p p.size+1))+1 := by
    unfold clock
    omega
  have hinverse : g^(q-1)%p < p := Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide : 0 < 2) hp)
  obtain ⟨lastCost,hlc,hl⟩ := tail_charged p q g beta (g^(q-1)%p) frame hb hinverse
  obtain ⟨powerCost,hpc,hpRun⟩ := BinaryModPower.charged p g (q-1).bits (frame 12) hp hg
  simp only [Nat.size_eq_bits_len,bitsValue_bits] at hpc hpRun
  have hpFrame := BitOracleStackFrame.run powerLayout BinaryModPower.code
    (BinaryModPower.clock p (q-1).size)
    (BinaryModPower.start g.bits (q-1).bits p.bits (frame 12))
    (powerFrame (inputWords p q g beta frame))
  rw [hpRun,map_pure] at hpFrame
  have hpHalt : ∀ out ∈ support
      (BitOracleMachine.run (BitOracleStackFrame.code powerLayout BinaryModPower.code)
        (BinaryModPower.clock p (q-1).size)
        (BitOracleStackFrame.embed powerLayout
          (BinaryModPower.start g.bits (q-1).bits p.bits (frame 12))
          (powerFrame (inputWords p q g beta frame)))), out.1.l = none := by
    rw [hpFrame]
    intro out ho
    obtain rfl := eq_of_mem_support_pure _ ho
    rfl
  have htHalt : ∀ out ∈ support
      (BitOracleMachine.run (BitOracleStackFrame.code powerLayout BinaryModPower.code)
        (BinaryModPower.clock p (q-1).size)
        (BitOracleStackFrame.embed powerLayout
          (BinaryModPower.start g.bits (q-1).bits p.bits (frame 12))
          (powerFrame (inputWords p q g beta frame)))),
      ∀ last ∈ support (BitOracleMachine.run code (BinaryModMultiply.clock p p.size+1)
        (BitOracleReturnLink.embed powerLabel (some 1) out.1)), last.1.l = none := by
    rw [hpFrame]
    intro out ho
    obtain rfl := eq_of_mem_support_pure _ ho
    rw [power_output,hl]
    intro last hh
    obtain rfl := eq_of_mem_support_pure _ hh
    rfl
  have hcombined := BitOracleReturnLink.run
    (BitOracleStackFrame.code powerLayout BinaryModPower.code) code powerLabel 1 power_code
    (BinaryModPower.clock p (q-1).size) (BinaryModMultiply.clock p p.size+1)
    (BitOracleStackFrame.embed powerLayout
      (BinaryModPower.start g.bits (q-1).bits p.bits (frame 12))
      (powerFrame (inputWords p q g beta frame))) hpHalt htHalt
  rw [hpFrame,pure_bind,power_input,power_output,hl,pure_bind] at hcombined
  refine ⟨3+(powerCost+lastCost),?_,?_⟩
  · have bound (a b : Nat) : 3+(32*a+(32*b+3)) ≤ 32*(a+b+2) := by omega
    exact (Nat.add_le_add_left (Nat.add_le_add hpc hlc) 3).trans (bound _ _)
  · rw [hclock,BitOracleMachine.run,entry_step,pure_bind,hcombined,pure_bind]
    rfl

/-- The charged equality determines the complete deterministic padded run. -/
theorem padded_run (p q g beta : Nat) (hp : 2 ≤ p) (hg : g < p) (hb : beta < p)
    (frame : Fin 20 → List Bool) :
    tick^[clock p q] (start (inputWords p q g beta frame)) =
      result (answer p q g beta).bits (inputWords p q g beta frame) := by
  obtain ⟨charge,_,he⟩ := charged p q g beta hp hg hb frame
  obtain ⟨actual,_,ha⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock p q) (start (inputWords p q g beta frame))
  change BitOracleMachine.run code (clock p q) (start (inputWords p q g beta frame)) =
    pure (tick^[clock p q] (start (inputWords p q g beta frame)),actual) at ha
  rw [he] at ha
  exact (Prod.mk.inj ((OracleComp.pure_inj _ _).mp ha)).1.symm

#print axioms charged
#print axioms padded_run
end ExplainableCrypto.Helios.Computational.PrimeAdjustedBetaMachine
