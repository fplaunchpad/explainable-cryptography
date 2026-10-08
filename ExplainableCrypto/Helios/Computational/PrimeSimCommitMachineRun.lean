import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachineComponents
import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachinePhases

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open Turing.TM2
set_option maxRecDepth 65536

/-- Reachable complement operands and every retained word match the actual
framed subroutine interface; its result is the complete next phase. -/
theorem complement_phase_run (p q g alpha e z0 : Nat) (he : e < q)
    (frame : Fin 11 → List Bool) :
    ∃ used ≤ ScalarComplementMachine.clock q,
      tick^[used] (phaseCfg p q g alpha e z0 frame 0 (some (complementLabel 0)) 2) =
      phaseCfg p q g alpha e z0 frame 1 (some 1) 2 := by
  let saved : Fin 30 → List Bool := fun k => phaseWords p q g alpha e z0 frame 0 (complementLayout (.inr k))
  obtain ⟨u,hu,hr⟩ := complement_run q e he saved
  have hs : TM2ReturnLink.embed complementLabel 1
      (TM2StackFrame.embed complementLayout (ScalarComplementMachine.start q.bits (uniformNatEncode e)) saved) =
      phaseCfg p q g alpha e z0 frame 0 (some (complementLabel 0)) 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed complementLabel 1
      (TM2StackFrame.embed complementLayout
        (ScalarComplementMachine.result q.bits (uniformNatEncode e) e.bits (q-e).bits) saved) =
      phaseCfg p q g alpha e z0 frame 1 (some 1) 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at hr⟩

/-- The first power consumes the reached z0 digit word and preserves the
original statement/transcript frame and all retained power operands. -/
theorem power0_phase_run (p q g alpha e z0 : Nat) (hp : 2 ≤ p) (hg : g < p)
    (frame : Fin 11 → List Bool) :
    ∃ used ≤ BinaryModPower.clock p z0.bits.length,
      tick^[used] (phaseCfg p q g alpha e z0 frame 5
        (some (powerLabel 0 (BinaryModPower.copyLabel 0 0))) 0) =
      phaseCfg p q g alpha e z0 frame 6 (some 3) 2 := by
  let saved : Fin 23 → List Bool := fun k => phaseWords p q g alpha e z0 frame 5 (powerLayout (.inr k))
  obtain ⟨u,hu,hr⟩ := power_run 0 p g z0.bits [] hp hg saved
  simp only [bitsValue_bits] at hr
  have hs : TM2ReturnLink.embed (powerLabel 0) (if (0 : Fin 2) == 0 then 3 else 4)
      (TM2StackFrame.embed powerLayout (BinaryModPower.start g.bits z0.bits p.bits []) saved) =
      phaseCfg p q g alpha e z0 frame 5 (some (powerLabel 0 (BinaryModPower.copyLabel 0 0))) 0 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed (powerLabel 0) (if (0 : Fin 2) == 0 then 3 else 4)
      (TM2StackFrame.embed powerLayout (BinaryModPower.result (g^z0%p).bits g.bits z0.bits p.bits []) saved) =
      phaseCfg p q g alpha e z0 frame 6 (some 3) 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at hr⟩

/-- The second power uses q-e as reached, including the full exponent q at
zero e, and returns its result with the first power and whole frame intact. -/
theorem power1_phase_run (p q g alpha e z0 : Nat) (hp : 2 ≤ p) (ha : alpha < p)
    (frame : Fin 11 → List Bool) :
    ∃ used ≤ BinaryModPower.clock p (q-e).bits.length,
      tick^[used] (phaseCfg p q g alpha e z0 frame 9
        (some (powerLabel 1 (BinaryModPower.copyLabel 0 0))) 0) =
      phaseCfg p q g alpha e z0 frame 10 (some 4) 2 := by
  let saved : Fin 23 → List Bool := fun k => phaseWords p q g alpha e z0 frame 9 (powerLayout (.inr k))
  obtain ⟨u,hu,hr⟩ := power_run 1 p alpha (q-e).bits [] hp ha saved
  simp only [bitsValue_bits] at hr
  have hs : TM2ReturnLink.embed (powerLabel 1) (if (1 : Fin 2) == 0 then 3 else 4)
      (TM2StackFrame.embed powerLayout (BinaryModPower.start alpha.bits (q-e).bits p.bits []) saved) =
      phaseCfg p q g alpha e z0 frame 9 (some (powerLabel 1 (BinaryModPower.copyLabel 0 0))) 0 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed (powerLabel 1) (if (1 : Fin 2) == 0 then 3 else 4)
      (TM2StackFrame.embed powerLayout
        (BinaryModPower.result (alpha^(q-e)%p).bits alpha.bits (q-e).bits p.bits []) saved) =
      phaseCfg p q g alpha e z0 frame 10 (some 4) 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at hr⟩

/-- The product uses the two reached power results; its multiplicand bound is
derived from the actual modular output rather than supplied by the caller. -/
theorem multiply_phase_run (p q g alpha e z0 : Nat) (hp : 2 ≤ p)
    (frame : Fin 11 → List Bool) :
    ∃ used ≤ BinaryModMultiply.clock p (alpha^(q-e)%p).bits.length,
      tick^[used] (phaseCfg p q g alpha e z0 frame 12
        (some (multiplyLabel (BinaryModMultiply.copyLabel 0))) 0) =
      phaseCfg p q g alpha e z0 frame 13 (some 5) 2 := by
  let saved : Fin 27 → List Bool := fun k => phaseWords p q g alpha e z0 frame 12 (multiplyLayout (.inr k))
  obtain ⟨u,hu,hr⟩ := multiply_run p (g^z0%p) (alpha^(q-e)%p).bits
    (Nat.mod_lt _ (by omega)) saved
  simp only [bitsValue_bits] at hr
  have hs : TM2ReturnLink.embed multiplyLabel 5
      (TM2StackFrame.embed multiplyLayout
        (BinaryModMultiply.start (g^z0%p).bits (alpha^(q-e)%p).bits p.bits) saved) =
      phaseCfg p q g alpha e z0 frame 12 (some (multiplyLabel (BinaryModMultiply.copyLabel 0))) 0 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed multiplyLabel 5
      (TM2StackFrame.embed multiplyLayout
        (BinaryModMultiply.result (((g^z0%p)*(alpha^(q-e)%p))%p).bits (g^z0%p).bits p.bits) saved) =
      phaseCfg p q g alpha e z0 frame 13 (some 5) 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at hr⟩

#print axioms complement_phase_run
#print axioms power0_phase_run
#print axioms power1_phase_run
#print axioms multiply_phase_run
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def transferBefore : Fin 9 → Fin 16 := ![1,3,4,6,7,8,10,11,13]
def transferAfter : Fin 9 → Fin 16 := ![2,4,5,7,8,9,11,12,14]
def transferPhaseBound (p q g alpha e z0 : Nat) : Fin 9 → Nat :=
  ![4*z0.size+6,2*g.size+4,2*p.size+4,3*(g^z0%p).size+4,
    g.size+2*alpha.size+4,z0.size+2*(q-e).size+4,
    3*(alpha^(q-e)%p).size+4,3*(g^z0%p).size+4,3*(answer p q g alpha e z0).size+4]

private theorem phase_transfer_words (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool)
    (which : Fin 9) :
    transferWords which (phaseWords p q g alpha e z0 frame (transferBefore which)) =
      phaseWords p q g alpha e z0 frame (transferAfter which) := by
  funext k
  fin_cases which <;> fin_cases k <;> rfl

private theorem phase_transfer_bound (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool)
    (which : Fin 9) :
    ((phaseWords p q g alpha e z0 frame (transferBefore which)) (transferDestination which)).length +
      (if consumes which then 3 else 2)*
        ((phaseWords p q g alpha e z0 frame (transferBefore which)) (transferSource which)).length+4 =
      transferPhaseBound p q g alpha e z0 which := by
  fin_cases which
  · change 0+2*(uniformNatEncode z0).length+4 = 4*z0.size+6
    rw [uniformNatEncode_length]
    omega
  · change 0+2*g.bits.length+4 = 2*g.size+4
    simp [Nat.size_eq_bits_len]
  · change 0+2*p.bits.length+4 = 2*p.size+4
    simp [Nat.size_eq_bits_len]
  · change 0+3*(g^z0%p).bits.length+4 = 3*(g^z0%p).size+4
    simp [Nat.size_eq_bits_len]
  · change g.bits.length+2*alpha.bits.length+4 = g.size+2*alpha.size+4
    simp [Nat.size_eq_bits_len]
  · change z0.bits.length+2*(q-e).bits.length+4 = z0.size+2*(q-e).size+4
    simp [Nat.size_eq_bits_len]
  · change 0+3*(alpha^(q-e)%p).bits.length+4 = 3*(alpha^(q-e)%p).size+4
    simp [Nat.size_eq_bits_len]
  · change 0+3*(g^z0%p).bits.length+4 = 3*(g^z0%p).size+4
    simp [Nat.size_eq_bits_len]
  · change 0+3*(answer p q g alpha e z0).bits.length+4 = 3*(answer p q g alpha e z0).size+4
    simp [Nat.size_eq_bits_len]

/-- Each concrete transfer call derives its complete reached successor and
actual replacement bound, including the nonempty base/exponent destinations. -/
theorem transfer_phase (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) (which : Fin 9) :
    ∃ used ≤ transferPhaseBound p q g alpha e z0 which,
      tick^[used] (phaseCfg p q g alpha e z0 frame (transferBefore which)
        (some (transferLabel which 0)) 0) =
      phaseCfg p q g alpha e z0 frame (transferAfter which) (some (transferReturn which)) 0 := by
  have hs : (phaseWords p q g alpha e z0 frame (transferBefore which)) 26 = [] := by
    fin_cases which <;> rfl
  obtain ⟨u,hu,he⟩ := transfer_slice which (phaseWords p q g alpha e z0 frame (transferBefore which)) hs
  rw [phase_transfer_bound] at hu
  rw [phase_transfer_words] at he
  exact ⟨u,hu,he⟩

/-- The actual saved z0 prefix gives the parser's empty suffix and scratch
conditions, and its complete successor is the phase entering guard two. -/
theorem parser_phase (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) :
    ∃ used ≤ 3*z0.size+3,
      tick^[used] (phaseCfg p q g alpha e z0 frame 2 (some (parseLabel 0)) 0) =
      phaseCfg p q g alpha e z0 frame 3 (some 2) 2 := by
  have hi : phaseWords p q g alpha e z0 frame 2 30 = uniformNatEncode z0++[] := by
    simp only [List.append_nil]
    rfl
  have hc : phaseWords p q g alpha e z0 frame 2 24 = [] := rfl
  have hs : phaseWords p q g alpha e z0 frame 2 25 = [] := rfl
  have ho : phaseWords p q g alpha e z0 frame 2 36 = [] := rfl
  obtain ⟨u,hu,he⟩ := parser_slice z0 [] (phaseWords p q g alpha e z0 frame 2) hi hc hs ho
  exact ⟨u,hu,he⟩

#print axioms transfer_phase
#print axioms parser_phase
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open Turing.TM2
set_option maxRecDepth 65536

def clearPort (which : Fin 6) : Fin 38 := ![29,33,34,36,1,9] which
def clearLabel (which : Fin 6) : Fin size := ⟨6+which.val,by have := which.isLt; unfold size; omega⟩
def clearNext (which : Fin 6) : Fin size := ⟨7+which.val,by have := which.isLt; unfold size; omega⟩
private theorem clear_code (which : Fin 6) : program (clearLabel which) =
    clear (clearPort which) (clearLabel which) (clearNext which) := by
  fin_cases which <;> rfl

private theorem clear_step (which : Fin 6) (words : Fin 38 → List Bool)
    (word : List Bool) (v : Fin 3) :
    tick ⟨some (clearLabel which),v,Function.update words (clearPort which) word⟩ =
      match word with
      | [] => ⟨some (clearNext which),0,Function.update words (clearPort which) []⟩
      | b::rest => ⟨some (clearLabel which),BinaryModuloCode.memory (some b),
          Function.update words (clearPort which) rest⟩ := by
  cases word with
  | nil => simp [tick,TM2ReturnLink.tick,clear_code,clear,enter,stepAux,BinaryModuloCode.memory]
  | cons b rest => cases b <;> simp [tick,TM2ReturnLink.tick,clear_code,clear,enter,stepAux,BinaryModuloCode.memory]

/-- Each actual cleanup loop consumes exactly its current word and leaves all
other ports untouched. These are the six fixed cleanup sites, not arbitrary code. -/
theorem clear_run (which : Fin 6) (words : Fin 38 → List Bool)
    (word : List Bool) (v : Fin 3) :
    tick^[word.length+1] ⟨some (clearLabel which),v,Function.update words (clearPort which) word⟩ =
      ⟨some (clearNext which),0,Function.update words (clearPort which) []⟩ := by
  induction word generalizing v with
  | nil => simpa using clear_step which words [] v
  | cons b rest ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,clear_step,ih]

#print axioms clear_run
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem clear_slice (which : Fin 6) (words : Fin 38 → List Bool) (v : Fin 3) :
    tick^[(words (clearPort which)).length+1] ⟨some (clearLabel which),v,words⟩ =
      ⟨some (clearNext which),0,Function.update words (clearPort which) []⟩ := by
  simpa only [Function.update_eq_self] using clear_run which words (words (clearPort which)) v

def guardPhase : Fin 6 → Fin 16 := ![0,1,3,6,10,13]
def guardNext : Fin 6 → Fin size :=
  ![complementLabel 0,transferLabel 0 0,transferLabel 1 0,transferLabel 3 0,transferLabel 6 0,transferLabel 8 0]
theorem guard_step (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) (which : Fin 6) :
    tick (phaseCfg p q g alpha e z0 frame (guardPhase which) (some ⟨which.val,by have := which.isLt; unfold size; omega⟩) 2) =
      phaseCfg p q g alpha e z0 frame (guardPhase which) (some (guardNext which))
        (if which == 0 then 2 else 0) := by
  fin_cases which <;> rfl

theorem final_step (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) :
    tick (phaseCfg p q g alpha e z0 frame 15 (some 12) 0) =
      phaseCfg p q g alpha e z0 frame 15 none 2 := rfl

#print axioms clear_slice
#print axioms guard_step
#print axioms final_step
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 0
private theorem sequence {a b : Nat} {initial middle final : Config}
    (ha : tick^[a] initial = middle) (hb : tick^[b] middle = final) :
    tick^[b+a] initial = final := by
  rw [Function.iterate_add_apply,ha,hb]

private theorem cleanup_words (words : Fin 38 → List Bool) :
    tick^[(words 29).length+(words 33).length+(words 34).length+
      (words 36).length+(words 1).length+(words 9).length+6]
      ⟨some 6,0,words⟩ =
    ⟨some 12,0,Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update words 29 []) 33 []) 34 []) 36 []) 1 []) 9 []⟩ := by
  let w1 := Function.update words 29 []
  let w2 := Function.update w1 33 []
  let w3 := Function.update w2 34 []
  let w4 := Function.update w3 36 []
  let w5 := Function.update w4 1 []
  let w6 := Function.update w5 9 []
  have h0 : tick^[(words 29).length+1] ⟨some 6,0,words⟩ = ⟨some 7,0,w1⟩ := clear_slice 0 words 0
  have h1 : tick^[(words 33).length+1] ⟨some 7,0,w1⟩ = ⟨some 8,0,w2⟩ := clear_slice 1 w1 0
  have h2 : tick^[(words 34).length+1] ⟨some 8,0,w2⟩ = ⟨some 9,0,w3⟩ := clear_slice 2 w2 0
  have h3 : tick^[(words 36).length+1] ⟨some 9,0,w3⟩ = ⟨some 10,0,w4⟩ := clear_slice 3 w3 0
  have h4 : tick^[(words 1).length+1] ⟨some 10,0,w4⟩ = ⟨some 11,0,w5⟩ := clear_slice 4 w4 0
  have h5 : tick^[(words 9).length+1] ⟨some 11,0,w5⟩ = ⟨some 12,0,w6⟩ := clear_slice 5 w5 0
  have h := sequence (sequence (sequence (sequence (sequence h0 h1) h2) h3) h4) h5
  convert h using 1
  congr 1
  omega

theorem cleanup_phase_run (p q g alpha e z0 : Nat) (frame : Fin 11 → List Bool) :
    tick^[p.bits.length+(g^z0%p).bits.length+alpha.bits.length+
      (q-e).bits.length+e.bits.length+(q-e).bits.length+6]
      (phaseCfg p q g alpha e z0 frame 14 (some 6) 0) =
      phaseCfg p q g alpha e z0 frame 15 (some 12) 0 := by
  exact cleanup_words (phaseWords p q g alpha e z0 frame 14)

#print axioms cleanup_phase_run
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
set_option maxHeartbeats 0
set_option maxRecDepth 65536
/-- Actual finite instruction audit; it does not assume a run or a cost certificate. -/
theorem local_cost (l : Fin size) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel
#print axioms local_cost
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
/-- Local arithmetic aggregation for this controller's actual phase bounds.
No execution premise is hidden here; callers supply already-proved numeric inequalities. -/
private theorem aggregate_clock_bound
    (P Q G A E Z D U V R C Pow Mul c a b m n t0 t1 t2 t3 t4 t5 t6 t7 t8 : Nat)
    (hG : G ≤ P) (hA : A ≤ P) (hE : E ≤ Q) (hZ : Z ≤ Q) (hD : D ≤ Q)
    (hU : U ≤ P) (hV : V ≤ P) (hR : R ≤ P)
    (hc : c ≤ C) (ha : a ≤ Pow) (hb : b ≤ Pow) (hm : m ≤ Mul)
    (hn : n ≤ 3*Z+3)
    (h0 : t0 ≤ 4*Z+6) (h1 : t1 ≤ 2*G+4) (h2 : t2 ≤ 2*P+4)
    (h3 : t3 ≤ 3*U+4) (h4 : t4 ≤ G+2*A+4) (h5 : t5 ≤ Z+2*D+4)
    (h6 : t6 ≤ 3*V+4) (h7 : t7 ≤ 3*U+4) (h8 : t8 ≤ 3*R+4) :
    1+((P+U+A+D+E+D+6)+(t8+(1+(m+(t7+(t6+(1+(b+(t5+(t4+(t3+(1+(a+(t2+(t1+(1+(n+(t0+(1+(c+(1))))))))))))))))))))) ≤
      C+2*Pow+Mul+22*P+13*Q+54 := by
  simp only [← Nat.add_assoc]
  omega
#print axioms aggregate_clock_bound
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
private theorem chain {a b : Nat} {initial middle final : Config}
    (ha : tick^[a] initial = middle) (hb : tick^[b] middle = final) :
    tick^[b+a] initial = final := by
  rw [Function.iterate_add_apply,ha,hb]

/-- Complete execution from the reached operand presentation. Every component
entry, scratch condition and retained frame is derived by the phase proofs. -/
theorem run (p q g alpha e z0 : Nat)
    (hp : 2 ≤ p) (hg : g < p) (ha : alpha < p) (he : e < q) (hz : z0 < q)
    (frame : Fin 11 → List Bool) :
    ∃ used ≤ clock p q,
      tick^[used] (start (inputWords p q g alpha e z0 frame)) =
        result (answer p q g alpha e z0).bits (inputWords p q g alpha e z0 frame) := by
  obtain ⟨c,hc,ec⟩ := complement_phase_run p q g alpha e z0 he frame
  obtain ⟨a,ha',ea⟩ := power0_phase_run p q g alpha e z0 hp hg frame
  obtain ⟨b,hb,eb⟩ := power1_phase_run p q g alpha e z0 hp ha frame
  obtain ⟨m,hm,em⟩ := multiply_phase_run p q g alpha e z0 hp frame
  obtain ⟨n,hn,en⟩ := parser_phase p q g alpha e z0 frame
  obtain ⟨t0,ht0,et0⟩ := transfer_phase p q g alpha e z0 frame 0
  obtain ⟨t1,ht1,et1⟩ := transfer_phase p q g alpha e z0 frame 1
  obtain ⟨t2,ht2,et2⟩ := transfer_phase p q g alpha e z0 frame 2
  obtain ⟨t3,ht3,et3⟩ := transfer_phase p q g alpha e z0 frame 3
  obtain ⟨t4,ht4,et4⟩ := transfer_phase p q g alpha e z0 frame 4
  obtain ⟨t5,ht5,et5⟩ := transfer_phase p q g alpha e z0 frame 5
  obtain ⟨t6,ht6,et6⟩ := transfer_phase p q g alpha e z0 frame 6
  obtain ⟨t7,ht7,et7⟩ := transfer_phase p q g alpha e z0 frame 7
  obtain ⟨t8,ht8,et8⟩ := transfer_phase p q g alpha e z0 frame 8
  have g0 : tick^[1] (phaseCfg p q g alpha e z0 frame 0 (some 0) 2) =
      phaseCfg p q g alpha e z0 frame 0 (some (complementLabel 0)) 2 := by
    rw [Function.iterate_one]
    exact guard_step p q g alpha e z0 frame 0
  have g1 : tick^[1] (phaseCfg p q g alpha e z0 frame 1 (some 1) 2) =
      phaseCfg p q g alpha e z0 frame 1 (some (transferLabel 0 0)) 0 := by
    rw [Function.iterate_one]
    exact guard_step p q g alpha e z0 frame 1
  have g2 : tick^[1] (phaseCfg p q g alpha e z0 frame 3 (some 2) 2) =
      phaseCfg p q g alpha e z0 frame 3 (some (transferLabel 1 0)) 0 := by
    rw [Function.iterate_one]
    exact guard_step p q g alpha e z0 frame 2
  have g3 : tick^[1] (phaseCfg p q g alpha e z0 frame 6 (some 3) 2) =
      phaseCfg p q g alpha e z0 frame 6 (some (transferLabel 3 0)) 0 := by
    rw [Function.iterate_one]
    exact guard_step p q g alpha e z0 frame 3
  have g4 : tick^[1] (phaseCfg p q g alpha e z0 frame 10 (some 4) 2) =
      phaseCfg p q g alpha e z0 frame 10 (some (transferLabel 6 0)) 0 := by
    rw [Function.iterate_one]
    exact guard_step p q g alpha e z0 frame 4
  have g5 : tick^[1] (phaseCfg p q g alpha e z0 frame 13 (some 5) 2) =
      phaseCfg p q g alpha e z0 frame 13 (some (transferLabel 8 0)) 0 := by
    rw [Function.iterate_one]
    exact guard_step p q g alpha e z0 frame 5
  have cleanup := cleanup_phase_run p q g alpha e z0 frame
  have final := final_step p q g alpha e z0 frame
  rw [← Function.iterate_one tick] at final
  have full := (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain (chain g0 ec) g1) et0) en) g2) et1) et2) ea) g3) et3) et4) et5) eb) g4) et6) et7) em) g5) et8) cleanup) final)
  rw [phase_start,phase_result] at full
  refine ⟨_,?_,full⟩
  clear ec ea eb em en et0 et1 et2 et3 et4 et5 et6 et7 et8 g0 g1 g2 g3 g4 g5 cleanup final full
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide : 0 < 2) hp
  have zg : g.size ≤ p.size := Nat.size_le_size (Nat.le_of_lt hg)
  have za : alpha.size ≤ p.size := Nat.size_le_size (Nat.le_of_lt ha)
  have ze : e.size ≤ q.size := Nat.size_le_size (Nat.le_of_lt he)
  have zz : z0.size ≤ q.size := Nat.size_le_size (Nat.le_of_lt hz)
  have zd : (q-e).size ≤ q.size := Nat.size_le_size (Nat.sub_le q e)
  have zu : (g^z0%p).size ≤ p.size := Nat.size_le_size (Nat.le_of_lt (Nat.mod_lt _ hp0))
  have zv : (alpha^(q-e)%p).size ≤ p.size := Nat.size_le_size (Nat.le_of_lt (Nat.mod_lt _ hp0))
  have zr : (answer p q g alpha e z0).size ≤ p.size :=
    Nat.size_le_size (Nat.le_of_lt (Nat.mod_lt _ hp0))
  simp only [Nat.size_eq_bits_len] at ha' hb hm ⊢
  have pa : BinaryModPower.clock p z0.size ≤ BinaryModPower.clock p q.size := by
    unfold BinaryModPower.clock
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 3 zz) 5)
      (Nat.mul_le_mul_right _ zz)
  have pb : BinaryModPower.clock p (q-e).size ≤ BinaryModPower.clock p q.size := by
    unfold BinaryModPower.clock
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 3 zd) 5)
      (Nat.mul_le_mul_right _ zd)
  have pm : BinaryModMultiply.clock p (alpha^(q-e)%p).size ≤ BinaryModMultiply.clock p p.size := by
    unfold BinaryModMultiply.clock
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ zv) _
  simp only [transferPhaseBound,Matrix.cons_val_zero] at ht0 ht1 ht2 ht3 ht4 ht5 ht6 ht7 ht8
  exact aggregate_clock_bound p.size q.size g.size alpha.size e.size z0.size
    (q-e).size (g^z0%p).size (alpha^(q-e)%p).size (answer p q g alpha e z0).size
    (ScalarComplementMachine.clock q) (BinaryModPower.clock p q.size)
    (BinaryModMultiply.clock p p.size) c a b m n t0 t1 t2 t3 t4 t5 t6 t7 t8
    zg za ze zz zd zu zv zr hc (ha'.trans pa) (hb.trans pb) (hm.trans pm)
    hn ht0 ht1 ht2 ht3 ht4 ht5 ht6 ht7 ht8

/-- Unused fuel is spent only at the final successful halt. -/
theorem padded_run (p q g alpha e z0 : Nat)
    (hp : 2 ≤ p) (hg : g < p) (ha : alpha < p) (he : e < q) (hz : z0 < q)
    (frame : Fin 11 → List Bool) :
    tick^[clock p q] (start (inputWords p q g alpha e z0 frame)) =
      result (answer p q g alpha e z0).bits (inputWords p q g alpha e z0 frame) := by
  obtain ⟨u,hu,hr⟩ := run p q g alpha e z0 hp hg ha he hz frame
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,hr]
  exact Function.iterate_fixed (by rfl) d

/-- Actual charged execution follows from the finite instruction audit and
complete run; no cost certificate is supplied by the caller. -/
theorem charged (p q g alpha e z0 : Nat)
    (hp : 2 ≤ p) (hg : g < p) (ha : alpha < p) (he : e < q) (hz : z0 < q)
    (frame : Fin 11 → List Bool) :
    ∃ charge ≤ cost p q,
      BitOracleMachine.run code (clock p q) (start (inputWords p q g alpha e z0 frame)) =
        pure (result (answer p q g alpha e z0).bits (inputWords p q g alpha e z0 frame),charge) := by
  obtain ⟨charge,hc,hr⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock p q) (start (inputWords p q g alpha e z0 frame))
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run code (clock p q) (start (inputWords p q g alpha e z0 frame)) =
    pure (tick^[clock p q] (start (inputWords p q g alpha e z0 frame)),charge) at hr
  rw [hr,padded_run p q g alpha e z0 hp hg ha he hz frame]

#print axioms run
#print axioms padded_run
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
