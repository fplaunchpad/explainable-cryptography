import Mathlib.Data.ZMod.Basic
import ExplainableCrypto.Helios.Computational.BinaryModAddMachine
import ExplainableCrypto.Helios.Computational.BinaryModMultiplyArithmetic

/-! Actual reduced-add and modular-difference execution with retained operands.
The multiplier supplies the prepared complement for reduced addition. The direct
difference interface accepts canonical operand digits and proves the zero case
through the same program. Enclosing callers still establish operand origins and
frames; the scalar specialization requires only a nonzero modulus. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModAddMachine
open Turing.TM2
set_option maxRecDepth 8192

private theorem sub_code (which : Fin 3) (l : Fin 11) :
    program (subLabel which l) = TM2ReturnLink.redirect (subLabel which) (subReturn which)
      (subProgram which l) := by fin_cases which <;> fin_cases l <;> rfl
private theorem copy_code (which : Fin 2) (l : Fin 2) :
    program (copyLabel which l) = TM2ReturnLink.redirect (copyLabel which) (copyReturn which)
      (copyProgram which l) := by fin_cases which <;> fin_cases l <;> rfl

private def subState (which : Fin 3) (label : Fin 42) (v : Fin 3)
    (xs ys out : List Bool) (frame : Fin 2 → List Bool) : Config :=
  ⟨some label,v,![![xs,ys,[],[],[],out,frame 0,frame 1],
    ![xs,frame 0,[],[],[],ys,frame 1,out],
    ![xs,frame 0,[],[],[],out,frame 1,ys]] which⟩

private theorem sub_run (which : Fin 3) (xs ys : List Bool) (frame : Fin 2 → List Bool) :
    ∃ used ≤ 3*(xs.length+ys.length)+5,
      tick^[used] (subState which (subLabel which 0) 0 xs ys [] frame) =
        subState which (subReturn which)
          (BinaryModuloCode.memory (some (decide (bitsValue ys ≤ bitsValue xs)))) [] ys
          (if bitsValue ys ≤ bitsValue xs then (bitsValue xs-bitsValue ys).bits else xs) frame := by
  obtain ⟨fuel,hf,he⟩ := BinarySubtractMachine.run xs ys
  have translated : (TM2ReturnLink.tick (subProgram which))^[fuel]
      (subPresent which (BinarySubtractMachine.state (some (.scan false)) xs ys [] [] [] []) frame) =
      subPresent which (BinarySubtractMachine.state none [] ys [] [] []
        (if bitsValue ys ≤ bitsValue xs then (bitsValue xs-bitsValue ys).bits else xs)
        (some (decide (bitsValue ys ≤ bitsValue xs)))) frame := by
    rw [subPresent,subProgram,TM2FiniteCoordinates.run,TM2StackFrame.run]
    exact congrArg (fun cfg => subPresent which cfg frame) he
  obtain ⟨used,hu,hs⟩ := TM2ReturnLink.run (subProgram which) program (subLabel which)
    (subReturn which) (sub_code which) fuel _ (by rw [translated]; rfl)
  rw [translated] at hs
  refine ⟨used,hu.trans hf,?_⟩
  have hi : TM2ReturnLink.embed (subLabel which) (subReturn which)
      (subPresent which (BinarySubtractMachine.state (some (.scan false)) xs ys [] [] [] []) frame) =
      subState which (subLabel which 0) 0 xs ys [] frame := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ho : ∀ out v, TM2ReturnLink.embed (subLabel which) (subReturn which)
      (subPresent which (BinarySubtractMachine.state none [] ys [] [] [] out v) frame) =
      subState which (subReturn which) (BinaryModuloCode.memory v) [] ys out frame := by
    intro out v
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  rwa [hi,ho] at hs

private def copyState (which : Fin 2) (label : Fin 42) (v : Fin 3)
    (source dest scratch : List Bool) (frame : Fin 5 → List Bool) : Config :=
  ⟨some label,v,![![dest,source,scratch,frame 0,frame 1,frame 2,frame 3,frame 4],
    ![dest,frame 0,scratch,frame 1,frame 2,frame 3,source,frame 4]] which⟩

private theorem copy_run (which : Fin 2) (source : List Bool) (frame : Fin 5 → List Bool) :
    ∃ used ≤ 2*source.length+2,
      tick^[used] (copyState which (copyLabel which 0) 0 source [] [] frame) =
        copyState which (copyReturn which) 0 source source [] frame := by
  have translated : (TM2ReturnLink.tick (copyProgram which))^[2*source.length+2]
      (copyPresent which (BitCopyMachine.config (some false) source [] []) frame) =
      copyPresent which (BitCopyMachine.config none source source []) frame := by
    rw [copyPresent,copyProgram,TM2FiniteCoordinates.run,TM2StackFrame.run]
    have h := BitCopyMachine.run source [] none
    change (TM2ReturnLink.tick BitCopyMachine.program)^[2*source.length+2] _ = _ at h
    rw [h]
    simp only [List.append_nil]
    rfl
  obtain ⟨used,hu,hs⟩ := TM2ReturnLink.run (copyProgram which) program (copyLabel which)
    (copyReturn which) (copy_code which) (2*source.length+2) _ (by rw [translated]; rfl)
  rw [translated] at hs
  refine ⟨used,hu,?_⟩
  have hi : TM2ReturnLink.embed (copyLabel which) (copyReturn which)
      (copyPresent which (BitCopyMachine.config (some false) source [] []) frame) =
      copyState which (copyLabel which 0) 0 source [] [] frame := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed (copyLabel which) (copyReturn which)
      (copyPresent which (BitCopyMachine.config none source source []) frame) =
      copyState which (copyReturn which) 0 source source [] frame := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  rwa [hi,ho] at hs

private theorem clear_run (port : Fin 8) (again next : Fin 42)
    (hc : program again = clear port again next) (word : List Bool)
    (other : Fin 8 → List Bool) (v : Fin 3) :
    tick^[word.length+1] ⟨some again,v,Function.update other port word⟩ =
      ⟨some next,0,Function.update other port []⟩ := by
  induction word generalizing v with
  | nil => simp [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory]
  | cons bit word ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    cases bit
    · simpa [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory] using ih 1
    · simpa [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory] using ih 2

private def moveState (label : Option (Fin 42)) (v : Fin 3)
    (xs ys zs c p : List Bool) : Config := ⟨label,v,![zs,c,[],ys,[],xs,p,[]]⟩
private theorem collect_step (b : Bool) (xs ys zs c p : List Bool) (v : Fin 3) :
    tick (moveState (some 3) v (b::xs) ys zs c p) =
      moveState (some 3) (if b then 2 else 1) xs (b::ys) zs c p := by
  cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem collect_empty (ys zs c p : List Bool) (v : Fin 3) :
    tick (moveState (some 3) v [] ys zs c p) = moveState (some 4) 0 [] ys zs c p := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl
private theorem restore_step (b : Bool) (xs ys zs c p : List Bool) (v : Fin 3) :
    tick (moveState (some 4) v xs (b::ys) zs c p) =
      moveState (some 4) (if b then 2 else 1) xs ys (b::zs) c p := by
  cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem restore_empty (xs zs c p : List Bool) (v : Fin 3) :
    tick (moveState (some 4) v xs [] zs c p) = moveState none 2 xs [] zs c p := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl
private theorem collect_run (xs ys zs c p : List Bool) (v : Fin 3) :
    tick^[xs.length+1] (moveState (some 3) v xs ys zs c p) =
      moveState (some 4) 0 [] (xs.reverse++ys) zs c p := by
  induction xs generalizing ys v with
  | nil => simp [collect_empty]
  | cons b xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply,collect_step,ih]
    simp [List.reverse_cons,List.append_assoc]
private theorem restore_run (xs ys zs c p : List Bool) (v : Fin 3) :
    tick^[ys.length+1] (moveState (some 4) v xs ys zs c p) =
      moveState none 2 xs [] (ys.reverse++zs) c p := by
  induction ys generalizing zs v with
  | nil => simp [restore_empty]
  | cons b ys ih =>
    rw [List.length_cons,Function.iterate_succ_apply,restore_step,ih]
    simp [List.reverse_cons,List.append_assoc]
private theorem finish (word c p : List Bool) :
    tick^[2*word.length+2] (moveState (some 3) 0 word [] [] c p) = result word c p := by
  rw [show 2*word.length+2 = (word.length+1)+(word.length+1) by omega,
    Function.iterate_add_apply,collect_run]
  simp only [List.append_nil]
  have h := restore_run [] word.reverse [] c p 0
  simpa only [List.length_reverse,List.reverse_reverse,List.append_nil,moveState,result] using h

private def boundary (label : Fin 42) (v : Fin 3) (lhs c answer p extra : List Bool) : Config :=
  ⟨some label,v,![lhs,c,[],[],[],answer,p,extra]⟩

private theorem clear_answer (word c p d : List Bool) (v : Fin 3) :
    tick^[word.length+1] (boundary 1 v [] c word p d) =
      boundary (copyLabel 1 0) 0 [] c [] p d := by
  have h := clear_run 5 1 (copyLabel 1 0) rfl word (boundary 1 0 [] c [] p d).stk v
  have hi : (⟨some 1,v,Function.update (boundary 1 0 [] c [] p d).stk 5 word⟩ : Config) =
      boundary 1 v [] c word p d := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : (⟨some (copyLabel 1 0),0,Function.update (boundary 1 0 [] c [] p d).stk 5 []⟩ : Config) =
      boundary (copyLabel 1 0) 0 [] c [] p d := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rwa [hi,ho] at h

private theorem clear_difference (word c p d : List Bool) (v : Fin 3) :
    tick^[d.length+1] (boundary 2 v [] c word p d) = boundary 3 0 [] c word p [] := by
  have h := clear_run 7 2 3 rfl d (boundary 2 0 [] c word p []).stk v
  have hi : (⟨some 2,v,Function.update (boundary 2 0 [] c word p []).stk 7 d⟩ : Config) =
      boundary 2 v [] c word p d := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : (⟨some 3,0,Function.update (boundary 2 0 [] c word p []).stk 7 []⟩ : Config) =
      boundary 3 0 [] c word p [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rwa [hi,ho] at h

private theorem sequence {a b c : Config} {n k : Nat}
    (h : tick^[n] a = b) (h' : tick^[k] b = c) : tick^[k+n] a = c := by
  rw [Function.iterate_add_apply,h,h']

/-- The program reaches its actual final halt within the public width bound.
Subroutine return clocks and all cleanup clocks are derived from execution. -/
theorem used_run (p x r : Nat) (hx : x < p) (hr : r < p) :
    ∃ used ≤ clock p,
      tick^[used] (start r.bits (p-x).bits p.bits) =
        result ((r+x)%p).bits (p-x).bits p.bits := by
  have hc : p-x ≤ p := Nat.sub_le _ _
  have hcW := Nat.size_le_size hc
  have hrW := Nat.size_le_size hr.le
  obtain ⟨u0,hu0,h0⟩ := sub_run 0 r.bits (p-x).bits ![p.bits,[]]
  simp only [bitsValue_bits,Nat.size_eq_bits_len] at hu0 h0
  by_cases h : p-x ≤ r
  · simp only [h,ite_true,decide_true] at h0
    change tick^[u0] (start r.bits (p-x).bits p.bits) =
      boundary 0 2 [] (p-x).bits (r-(p-x)).bits p.bits [] at h0
    have gate : tick^[1] (boundary 0 2 [] (p-x).bits (r-(p-x)).bits p.bits []) =
        boundary 3 0 [] (p-x).bits (r-(p-x)).bits p.bits [] := by rfl
    have done := finish (r-(p-x)).bits (p-x).bits p.bits
    change tick^[2*(r-(p-x)).bits.length+2]
      (boundary 3 0 [] (p-x).bits (r-(p-x)).bits p.bits []) = _ at done
    have answer := BinaryModMultiplyArithmetic.reducedAdd_eq_mod p x r hx hr
    simp only [BinaryModMultiplyArithmetic.reducedAdd,h,ite_true] at answer
    have hsW := Nat.size_le_size ((Nat.sub_le r (p-x)).trans hr.le)
    refine ⟨(2*(r-(p-x)).bits.length+2)+(1+u0),?_,?_⟩
    · simp only [Nat.size_eq_bits_len,clock]; omega
    · have he := sequence h0 (sequence gate done)
      simpa only [Nat.add_assoc] using he.trans (congrArg (fun n => result n.bits (p-x).bits p.bits) answer)
  · have hrc : r ≤ p-x := by omega
    have hd : (p-x)-r ≤ p := (Nat.sub_le _ _).trans hc
    have hdW := Nat.size_le_size hd
    have haW := Nat.size_le_size (Nat.sub_le p ((p-x)-r))
    simp only [h,ite_false,decide_false] at h0
    change tick^[u0] (start r.bits (p-x).bits p.bits) =
      boundary 0 1 [] (p-x).bits r.bits p.bits [] at h0
    have gate : tick^[1] (boundary 0 1 [] (p-x).bits r.bits p.bits []) =
        boundary (copyLabel 0 0) 0 [] (p-x).bits r.bits p.bits [] := by rfl
    obtain ⟨v0,hv0,hcopy0⟩ := copy_run 0 (p-x).bits ![[],[],r.bits,p.bits,[]]
    change tick^[v0] (boundary (copyLabel 0 0) 0 [] (p-x).bits r.bits p.bits []) =
      boundary (subLabel 1 0) 0 (p-x).bits (p-x).bits r.bits p.bits [] at hcopy0
    obtain ⟨u1,hu1,h1⟩ := sub_run 1 (p-x).bits r.bits ![(p-x).bits,p.bits]
    simp only [bitsValue_bits,hrc,ite_true,decide_true] at h1
    change tick^[u1] (boundary (subLabel 1 0) 0 (p-x).bits (p-x).bits r.bits p.bits []) =
      boundary 1 2 [] (p-x).bits r.bits p.bits ((p-x)-r).bits at h1
    have hclear0 := clear_answer r.bits (p-x).bits p.bits ((p-x)-r).bits 2
    obtain ⟨v1,hv1,hcopy1⟩ := copy_run 1 p.bits ![(p-x).bits,[],[],[],((p-x)-r).bits]
    change tick^[v1] (boundary (copyLabel 1 0) 0 [] (p-x).bits [] p.bits ((p-x)-r).bits) =
      boundary (subLabel 2 0) 0 p.bits (p-x).bits [] p.bits ((p-x)-r).bits at hcopy1
    obtain ⟨u2,hu2,h2⟩ := sub_run 2 p.bits ((p-x)-r).bits ![(p-x).bits,p.bits]
    simp only [bitsValue_bits,hd,ite_true,decide_true] at h2
    change tick^[u2] (boundary (subLabel 2 0) 0 p.bits (p-x).bits [] p.bits ((p-x)-r).bits) =
      boundary 2 2 [] (p-x).bits (p-((p-x)-r)).bits p.bits ((p-x)-r).bits at h2
    have hclear1 := clear_difference (p-((p-x)-r)).bits (p-x).bits p.bits ((p-x)-r).bits 2
    have done := finish (p-((p-x)-r)).bits (p-x).bits p.bits
    change tick^[2*(p-((p-x)-r)).bits.length+2]
      (boundary 3 0 [] (p-x).bits (p-((p-x)-r)).bits p.bits []) = _ at done
    have he := sequence h0 (sequence gate (sequence hcopy0 (sequence h1
      (sequence hclear0 (sequence hcopy1 (sequence h2 (sequence hclear1 done)))))))
    have answer := BinaryModMultiplyArithmetic.reducedAdd_eq_mod p x r hx hr
    simp only [BinaryModMultiplyArithmetic.reducedAdd,h,ite_false] at answer
    refine ⟨_,?_,he.trans (congrArg (fun n => result n.bits (p-x).bits p.bits) answer)⟩
    simp only [Nat.size_eq_bits_len] at hv0 hv1 hu1 hu2 ⊢
    unfold clock
    omega

/-- Only the final halted configuration is padded to the advertised clock. -/
theorem run (p x r : Nat) (hx : x < p) (hr : r < p) :
    tick^[clock p] (start r.bits (p-x).bits p.bits) =
      result ((r+x)%p).bits (p-x).bits p.bits := by
  obtain ⟨used,hu,he⟩ := used_run p x r hx hr
  obtain ⟨extra,hclock⟩ := Nat.exists_eq_add_of_le hu
  have hh : tick (result ((r+x)%p).bits (p-x).bits p.bits) =
      result ((r+x)%p).bits (p-x).bits p.bits := rfl
  rw [hclock,Nat.add_comm used extra,Function.iterate_add_apply,he]
  exact Function.iterate_fixed hh extra

/-- A fixed local operation bound follows from all 42 actual instructions. -/
theorem local_cost (label : Fin 42) : BitOracleMachine.localCost (program label) ≤ 32 := by
  fin_cases label <;> decide +kernel

/-- The charged raw execution uses the same complete deterministic run. -/
theorem charged (p x r : Nat) (hx : x < p) (hr : r < p) :
    ∃ charge ≤ 32*clock p,
      BitOracleMachine.run code (clock p) (start r.bits (p-x).bits p.bits) =
        pure (result ((r+x)%p).bits (p-x).bits p.bits,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost (clock p)
    (start r.bits (p-x).bits p.bits)
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run code (clock p) (start r.bits (p-x).bits p.bits) =
    pure (tick^[clock p] (start r.bits (p-x).bits p.bits),charge) at he
  rw [he,run p x r hx hr]

/-- Equality at the complement threshold wraps to canonical zero, retaining
the complement and the four-bit modulus. -/
theorem wrap_control : tick^[128] (start [true,true,true] [true,true,true] [false,false,false,true]) =
    (⟨none,2,![[],[true,true,true],[],[],[],[],[false,false,false,true],[]]⟩ : Config) := by
  exact run 8 1 7 (by decide) (by decide)

/-- The underflow route computes one plus one modulo three, returning the
nonpalindromic word 01 and clearing all transient workspace. -/
theorem underflow_control : tick^[76] (start [true] [false,true] [true,true]) =
    (⟨none,2, ![[false,true],[false,true],[],[],[],[],[true,true],[]]⟩ : Config) := by
  exact run 3 1 1 (by decide) (by decide)

private def skipUnderflow (label : Fin 42) := if label = 0 then enter 3 else program label
private def skippedReadout :=
  let cfg := (TM2ReturnLink.tick skipUnderflow)^[76] (start [true] [false,true] [true,true])
  (cfg.var.val,cfg.stk 0,cfg.stk 1,cfg.stk 6)

/-- Actual gate mutation loses the addition on the same underflow fixture,
while returning success and retaining the right public operands. -/
theorem skipped_underflow_counterexample : skippedReadout =
    (2,[true],[false,true],[true,true]) := by decide +kernel

#print axioms local_cost
#print axioms charged
#print axioms wrap_control
#print axioms underflow_control
#print axioms skipped_underflow_counterexample
#print axioms used_run
#print axioms run
end ExplainableCrypto.Helios.Computational.BinaryModAddMachine

namespace ExplainableCrypto.Helios.Computational.BinaryModAddMachine
open Turing.TM2
set_option maxRecDepth 8192

/-- The zero complement follows the actual subtraction-success and restore
instructions. It does not satisfy the earlier reduced-add operand premise. -/
private theorem zero_complement_used_run (q c : Nat) (hc : c < q) :
    ∃ used ≤ clock q,
      tick^[used] (start c.bits [] q.bits) = result c.bits [] q.bits := by
  obtain ⟨u,hu,he⟩ := sub_run 0 c.bits [] ![q.bits,[]]
  simp only [bitsValue_bits,show bitsValue [] = 0 from rfl,Nat.zero_le,
    ite_true,decide_true,Nat.sub_zero,List.length_nil,Nat.add_zero] at hu he
  change tick^[u] (start c.bits [] q.bits) = boundary 0 2 [] [] c.bits q.bits [] at he
  have gate : tick^[1] (boundary 0 2 [] [] c.bits q.bits []) =
      boundary 3 0 [] [] c.bits q.bits [] := by rfl
  have done := finish c.bits [] q.bits
  change tick^[2*c.bits.length+2] (boundary 3 0 [] [] c.bits q.bits []) = _ at done
  have full := sequence he (sequence gate done)
  refine ⟨_,?_,full⟩
  have hw : c.size ≤ q.size := Nat.size_le_size hc.le
  simp only [Nat.size_eq_bits_len] at hu ⊢
  unfold clock
  omega

private theorem zero_complement_run (q c : Nat) (hc : c < q) :
    tick^[clock q] (start c.bits [] q.bits) = result c.bits [] q.bits := by
  obtain ⟨u,hu,he⟩ := zero_complement_used_run q c hc
  obtain ⟨extra,hclock⟩ := Nat.exists_eq_add_of_le hu
  rw [hclock,Nat.add_comm u extra,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) extra

/-- The unchanged controller also computes modular difference from direct
canonical operands. Zero uses its actual executed success path; no new code
or reduced-input assertion is supplied. -/
theorem difference_run (q c e : Nat) (hc : c < q) (he : e < q) :
    tick^[clock q] (start c.bits e.bits q.bits) =
      result ((c+q-e)%q).bits e.bits q.bits := by
  by_cases hz : e = 0
  · subst e
    simpa only [show (0 : Nat).bits = [] from rfl,Nat.sub_zero,Nat.add_mod_right,Nat.mod_eq_of_lt hc] using
      zero_complement_run q c hc
  · have hx : q-e < q := by omega
    have hcomplement : q-(q-e) = e := by omega
    have hsum : c+(q-e) = c+q-e := by omega
    simpa only [hcomplement,hsum] using run q (q-e) c hx hc

/-- Exact charged execution and the original instruction cap accompany the
new direct-difference interface; this is not a caller-supplied cost bound. -/
theorem difference_charged (q c e : Nat) (hc : c < q) (he : e < q) :
    ∃ charge ≤ 32*clock q,
      BitOracleMachine.run code (clock q) (start c.bits e.bits q.bits) =
        pure (result ((c+q-e)%q).bits e.bits q.bits,charge) := by
  obtain ⟨charge,hcost,hexec⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock q) (start c.bits e.bits q.bits)
  refine ⟨charge,hcost,?_⟩
  change BitOracleMachine.run code (clock q) (start c.bits e.bits q.bits) =
    pure (tick^[clock q] (start c.bits e.bits q.bits),charge) at hexec
  rw [hexec,difference_run q c e hc he]

private theorem scalar_difference_value {q : Nat} [NeZero q] (c e : ZMod q) :
    (c-e).val = (c.val+q-e.val)%q := by
  have he : e.val ≤ c.val+q := by have := ZMod.val_lt e; omega
  have hcast : ((c.val+q-e.val : Nat) : ZMod q) = c-e := by
    rw [Nat.cast_sub he]
    simp
  rw [←hcast,ZMod.val_natCast]

/-- Existing canonical scalar values give the actual field subtraction.
An enclosing parser still must execute their extraction and full frame. -/
theorem difference_source {q : Nat} [NeZero q] (c e : ZMod q) :
    tick^[clock q] (start c.val.bits e.val.bits q.bits) =
      result (c-e).val.bits e.val.bits q.bits := by
  rw [scalar_difference_value]
  exact difference_run q c.val e.val (ZMod.val_lt _) (ZMod.val_lt _)

theorem difference_charged_source {q : Nat} [NeZero q] (c e : ZMod q) :
    ∃ charge ≤ 32*clock q,
      BitOracleMachine.run code (clock q) (start c.val.bits e.val.bits q.bits) =
        pure (result (c-e).val.bits e.val.bits q.bits,charge) := by
  rw [scalar_difference_value]
  exact difference_charged q c.val e.val (ZMod.val_lt _) (ZMod.val_lt _)

#print axioms zero_complement_used_run
#print axioms difference_run
#print axioms difference_charged
#print axioms difference_source
#print axioms difference_charged_source
end ExplainableCrypto.Helios.Computational.BinaryModAddMachine

namespace ExplainableCrypto.Helios.Computational.BinaryModAddMachine
private def differenceView (cfg : Config) := (cfg.l.map Fin.val,cfg.var.val,List.ofFn cfg.stk)

/-- Independent complete reduction checks the previously uncovered e=0 endpoint. -/
theorem difference_zero_endpoint_control :
    differenceView (tick^[clock 3] (start [true] [] [true,true])) =
      (none,2,[[true],[],[],[],[],[],[true,true],[]]) := by decide +kernel

/-- Equal operands return canonical empty zero, retaining the second operand. -/
theorem difference_equal_control :
    differenceView (tick^[clock 3] (start [false,true] [false,true] [true,true])) =
      (none,2,[[],[false,true],[],[],[],[],[true,true],[]]) := by decide +kernel

private def omitDifferenceRestore (l : Fin 42) :=
  if l == 4 then Turing.TM2.Stmt.load (fun _ => 2) .halt else program l

/-- Actual restore omission fails at the zero endpoint despite successful halt. -/
theorem difference_zero_restore_counterexample :
    differenceView ((TM2ReturnLink.tick omitDifferenceRestore)^[clock 3]
      (start [true] [] [true,true])) =
      (none,2,[[],[],[],[true],[],[],[true,true],[]]) := by decide +kernel

#print axioms difference_zero_endpoint_control
#print axioms difference_equal_control
#print axioms difference_zero_restore_counterexample
end ExplainableCrypto.Helios.Computational.BinaryModAddMachine
