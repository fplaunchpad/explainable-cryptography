import ExplainableCrypto.Helios.Computational.PrimeNonceMachine
import ExplainableCrypto.Helios.Computational.PrimeSamplers

namespace ExplainableCrypto.Helios.Computational.PrimeNonceMachine
open Turing.TM2

private theorem prep_code (l : Fin 15) : program (prepLabel l) =
    TM2ReturnLink.redirect prepLabel 16 (SamplerOperands.compiled l) := by
  fin_cases l <;> rfl
private theorem writer_code (l : Fin 8) : program (writeLabel l) =
    TM2ReturnLink.redirect writeLabel 25 (writer l) := by
  fin_cases l <;> rfl

private def clearing (digits width suffix : List Bool) (frame : Frame) (v : Fin 3) : Config :=
  ⟨some 16,v,![[],digits,width,[],suffix,frame 0,frame 1,frame 2]⟩
private def writing (cfg : ScalarWriteCode.Config) : Config :=
  TM2ReturnLink.embed writeLabel 25
    (TM2FiniteCoordinates.present writerPorts (Equiv.refl _) (Equiv.refl _) cfg)

private theorem clear_run (width digits suffix : List Bool) (frame : Frame) (v : Fin 3) :
    (TM2ReturnLink.tick program)^[width.length+1] (clearing digits width suffix frame v) =
      writing (ScalarWriteCode.start digits (frame 0) suffix (frame 1) (frame 2)) := by
  induction width generalizing v with
  | nil =>
    simp [TM2ReturnLink.tick,program,clearing,step,stepAux,writing,
      ScalarWriteCode.start,TM2ReturnLink.embed,TM2FiniteCoordinates.present,
      writerPorts,writeLabel,CoinWordLoader.encode]
    funext k; fin_cases k <;> rfl
  | cons b bs ih =>
    have hs : TM2ReturnLink.tick program (clearing digits (b::bs) suffix frame v) =
        clearing digits bs suffix frame (CoinWordLoader.encode (some b)) := by
      cases b <;> simp [TM2ReturnLink.tick,program,clearing,step,stepAux,CoinWordLoader.encode]
      all_goals funext k; fin_cases k <;> rfl
    rw [List.length_cons,Function.iterate_succ_apply,hs,ih]

private theorem prepared (n : Nat) (suffix : List Bool) (frame : Frame) :
    ∃ used ≤ SamplerOperands.clock true 0 n,
      (TM2ReturnLink.tick program)^[used]
        (TM2ReturnLink.embed prepLabel 16 (SamplerOperands.present
          (SamplerOperands.start true (SamplerOperands.input 0 n suffix) frame))) =
        clearing (n+1).bits (List.replicate (n+1).size true) suffix frame 0 := by
  have hr : (TM2ReturnLink.tick SamplerOperands.compiled)^[SamplerOperands.clock true 0 n]
      (SamplerOperands.present (SamplerOperands.start true (SamplerOperands.input 0 n suffix) frame)) =
      SamplerOperands.present (SamplerOperands.result 0 (n+1) suffix frame) := by
    rw [SamplerOperands.compiled,SamplerOperands.present,TM2FiniteCoordinates.run]
    exact congrArg SamplerOperands.present (SamplerOperands.run_fixed true 0 n (by simp [SamplerOperands.range]) suffix frame)
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run SamplerOperands.compiled program prepLabel 16 prep_code
    (SamplerOperands.clock true 0 n) _ (by rw [hr]; rfl)
  refine ⟨u,hu,?_⟩
  rw [hr] at he
  refine he.trans ?_
  change (⟨some 16,0,_⟩ : Config) = ⟨some 16,0,_⟩
  congr 1

private theorem written (n : Nat) (suffix : List Bool) (frame : Frame) :
    ∃ used ≤ 3*n.size+3,
      (TM2ReturnLink.tick program)^[used]
        (writing (ScalarWriteCode.start n.bits (frame 0) suffix (frame 1) (frame 2))) =
        writing (ScalarWriteCode.result (uniformNatEncode n++suffix) (frame 0) (frame 1) (frame 2)) := by
  have hr := TM2FiniteCoordinates.run writerPorts (Equiv.refl _) (Equiv.refl _)
    ScalarWriteCode.program (3*n.size+3)
    (ScalarWriteCode.start n.bits (frame 0) suffix (frame 1) (frame 2))
  rw [ScalarWriteCode.run_digits] at hr
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run writer program writeLabel 25 writer_code
    (3*n.size+3)
    (TM2FiniteCoordinates.present writerPorts (Equiv.refl _) (Equiv.refl _)
      (ScalarWriteCode.start n.bits (frame 0) suffix (frame 1) (frame 2)))
    (by rw [writer,hr]; rfl)
  exact ⟨u,hu,by simpa only [writing,writer,hr] using he⟩

private theorem entry (n : Nat) (suffix : List Bool) (frame : Frame) :
    TM2ReturnLink.tick program (start (uniformNatEncode n++suffix) frame) =
      TM2ReturnLink.embed prepLabel 16 (SamplerOperands.present
        (SamplerOperands.start true (SamplerOperands.input 0 n suffix) frame)) := by
  simp [TM2ReturnLink.tick,program,start,step,stepAux,TM2ReturnLink.embed,
    SamplerOperands.present,SamplerOperands.start,SamplerOperands.state,SamplerOperands.input,
    SamplerOperands.labels,TM2FiniteCoordinates.present,BinaryModuloCode.memory]
  funext k; fin_cases k <;> rfl

private theorem exit (word : List Bool) (frame : Frame) :
    TM2ReturnLink.tick program (writing (ScalarWriteCode.result word (frame 0) (frame 1) (frame 2))) =
      result word frame := by
  simp [TM2ReturnLink.tick,program,writing,ScalarWriteCode.result,result,
    TM2ReturnLink.embed,TM2FiniteCoordinates.present,writerPorts,step,stepAux]
  funext k; fin_cases k <;> rfl

/-- Complete actual successor execution, with full frame and scratch state.
Only the final halted configuration is padded to the analysis clock. -/
theorem run_nat (n : Nat) (suffix : List Bool) (frame : Frame) :
    (TM2ReturnLink.tick program)^[clock n] (start (uniformNatEncode n++suffix) frame) =
      result (uniformNatEncode (n+1)++suffix) frame := by
  obtain ⟨p,hp,he⟩ := prepared n suffix frame
  obtain ⟨w,hw,hwRun⟩ := written (n+1) suffix frame
  have hr : (TM2ReturnLink.tick program)^[1+(w+((n+1).size+1)+(p+1))]
      (start (uniformNatEncode n++suffix) frame) = result (uniformNatEncode (n+1)++suffix) frame := by
    have hc := clear_run (List.replicate (n+1).size true) (n+1).bits suffix frame 0
    simp only [List.length_replicate] at hc
    simp only [Function.iterate_add_apply,Function.iterate_one]
    rw [entry,he]
    -- Keep the complete cleanup iteration intact when using its exact boundary.
    have hc' := hc
    simp only [Function.iterate_add_apply,Function.iterate_one] at hc'
    rw [hc',hwRun]
    exact exit _ _

  have hb : 1+(w+((n+1).size+1)+(p+1)) ≤ clock n := by unfold clock; omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hb
  rw [hd,Nat.add_comm _ d,Function.iterate_add_apply,hr]
  exact Function.iterate_fixed (by rfl) d

/-- The original historical nonce response, including q=2, is obtained by
executing the successor rather than casting a host-computed response. -/
theorem successor_run {q : Nat} [Fact q.Prime] (i : Fin (q-1))
    (suffix : List Bool) (frame : Frame) :
    (TM2ReturnLink.tick program)^[clock i.val] (start (uniformNatEncode i.val++suffix) frame) =
      result (scalarEncode (primeNonceValue i)++suffix) frame := by
  have hi : i.val+1 < q := by have := i.isLt; omega
  simpa only [scalarEncode,primeNonceValue,ZMod.val_natCast_of_lt hi] using run_nat i.val suffix frame

/-- Bound the actual statements, including the entry/cleanup/exit instructions. -/
theorem local_cost (l : Fin 26) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- No caller-supplied cost certificate: the charged execution follows from
actual instruction costs and the complete fixed-program run. -/
theorem charged (n : Nat) (suffix : List Bool) (frame : Frame) :
    ∃ charge ≤ 32*clock n,
      BitOracleMachine.run (fun l => .compute (program l)) (clock n)
        (start (uniformNatEncode n++suffix) frame) =
      pure (result (uniformNatEncode (n+1)++suffix) frame,charge) := by
  obtain ⟨c,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock n) (start (uniformNatEncode n++suffix) frame)
  exact ⟨c,hc,by simpa only [run_nat] using he⟩

#print axioms run_nat
#print axioms successor_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeNonceMachine
