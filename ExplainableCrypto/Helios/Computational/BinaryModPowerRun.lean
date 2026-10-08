import ExplainableCrypto.Helios.Computational.BinaryModPower
import ExplainableCrypto.Helios.Computational.BinaryModMultiplyRun
import ExplainableCrypto.Helios.Computational.BinaryModPowerArithmetic

/-! Full loaded square-and-multiply execution with retained base, exponent and
caller context. All copy, frame, width and return conditions come from execution. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModPower
open Turing.TM2
set_option maxRecDepth 8192

private theorem copy_code (which : Fin 5) (l : Fin 2) : program (copyLabel which l) =
    TM2ReturnLink.redirect (copyLabel which) (copyReturn which) (copyProgram which l) := by
  fin_cases which <;> fin_cases l <;> rfl
private theorem multiply_code (product : Bool) (l : Fin 86) : program (multiplyLabel product l) =
    TM2ReturnLink.redirect (multiplyLabel product) (if product then 8 else 4) (multiplyProgram l) := by
  cases product <;> fin_cases l <;> rfl

/-- The resident interface includes every work and retained port. -/
def state (l : Option (Fin 192)) (a raw operand base pending exponent modulus context : List Bool)
    (v : Fin 3 := 0) : Config :=
  ⟨l,v,![a,[],[],[],[],[],modulus,[],raw,[],operand,base,pending,exponent,context]⟩

private theorem sequence {a b c : Config} {n k : Nat}
    (h : tick^[n] a = b) (h' : tick^[k] b = c) : tick^[k+n] a = c := by
  rw [Function.iterate_add_apply,h,h']

private def copyWord (which : Fin 5) (a base exponent : List Bool) :=
  ![exponent,a,a,a,base] which
private def copyFrame (which : Fin 5) (a raw operand base pending exponent modulus context : List Bool) :
    Fin 7 → List Bool :=
  ![![a,modulus,[],operand,base,pending,context],
    ![modulus,raw,[],base,pending,exponent,context],
    ![modulus,[],operand,base,pending,exponent,context],
    ![modulus,raw,[],base,pending,exponent,context],
    ![a,modulus,[],operand,pending,exponent,context]] which

private theorem copy_run (which : Fin 5) (a raw operand base pending exponent modulus context : List Bool) :
    ∃ used ≤ 2*(copyWord which a base exponent).length+2,
      tick^[used] (state (some (copyLabel which 0)) a (![[],raw,[],raw,[]] which)
        (![operand,[],operand,[],operand] which) base pending exponent modulus context) =
      state (some (copyReturn which)) a (![exponent,raw,a,raw,base] which)
        (![operand,a,operand,a,operand] which) base pending exponent modulus context := by
  let word := copyWord which a base exponent
  let frame := copyFrame which a raw operand base pending exponent modulus context
  let initial := BinaryModAddMachine.copyPresent 1 (BitCopyMachine.config (some false) word [] []) (fun _ => [])
  let final := BinaryModAddMachine.copyPresent 1 (BitCopyMachine.config none word word []) (fun _ => [])
  have hi : (TM2ReturnLink.tick (BinaryModAddMachine.copyProgram 1))^[2*word.length+2] initial = final := by
    dsimp only [initial]
    rw [BinaryModAddMachine.copyProgram,BinaryModAddMachine.copyPresent,
      TM2FiniteCoordinates.run,TM2StackFrame.run]
    rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*word.length+2]
      (BitCopyMachine.config (some false) word [] []) =
      BitCopyMachine.config none word (word++[]) [] from BitCopyMachine.run word [] none]
    simp only [List.append_nil]
    rfl
  have hf := TM2StackFrame.run (copyLayout which) (BinaryModAddMachine.copyProgram 1)
    (2*word.length+2) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick (copyProgram which))^[2*word.length+2]
    (TM2StackFrame.embed (copyLayout which) initial frame) =
      TM2StackFrame.embed (copyLayout which) final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run (copyProgram which) program (copyLabel which)
    (copyReturn which) (copy_code which) (2*word.length+2) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed (copyLabel which) (copyReturn which)
      (TM2StackFrame.embed (copyLayout which) initial frame) =
      state (some (copyLabel which 0)) a (![[],raw,[],raw,[]] which)
        (![operand,[],operand,[],operand] which) base pending exponent modulus context := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed (copyLabel which) (copyReturn which)
      (TM2StackFrame.embed (copyLayout which) final frame) =
      state (some (copyReturn which)) a (![exponent,raw,a,raw,base] which)
        (![operand,a,operand,a,operand] which) base pending exponent modulus context := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

private theorem reverse_step (bit : Bool) (raw base pending exponent modulus context : List Bool) (v : Fin 3) :
    tick (state (some 0) [] (bit::raw) [] base pending exponent modulus context v) =
      state (some 0) [] raw [] base (bit::pending) exponent modulus context (if bit then 2 else 1) := by
  cases bit <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem reverse_empty (base pending exponent modulus context : List Bool) (v : Fin 3) :
    tick (state (some 0) [] [] [] base pending exponent modulus context v) =
      state (some 1) [] [] [] base pending exponent modulus context := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl
private theorem reverse_run (raw base pending exponent modulus context : List Bool) (v : Fin 3) :
    tick^[raw.length+1] (state (some 0) [] raw [] base pending exponent modulus context v) =
      state (some 1) [] [] [] base (raw.reverse++pending) exponent modulus context := by
  induction raw generalizing pending v with
  | nil => simpa using reverse_empty base pending exponent modulus context v
  | cons bit raw ih =>
    rw [List.length_cons,Function.iterate_succ_apply,reverse_step,ih]
    simp [List.reverse_cons,List.append_assoc]

private theorem prepare (base exponent modulus context : List Bool) :
    ∃ used ≤ 3*exponent.length+4,
      tick^[used] (start base exponent modulus context) =
        state (some 2) [true] [] [] base exponent.reverse exponent modulus context := by
  obtain ⟨u,hu,hcopy⟩ := copy_run 0 [] [] [] base [] exponent modulus context
  change tick^[u] (start base exponent modulus context) =
    state (some 0) [] exponent [] base [] exponent modulus context at hcopy
  have hreverse := reverse_run exponent base [] exponent modulus context 0
  simp only [List.append_nil] at hreverse
  have init : tick^[1] (state (some 1) [] [] [] base exponent.reverse exponent modulus context) =
      state (some 2) [true] [] [] base exponent.reverse exponent modulus context := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  refine ⟨1+(exponent.length+1)+u,?_,?_⟩
  · change u ≤ 2*exponent.length+2 at hu
    omega
  · exact sequence hcopy (sequence hreverse init)

private theorem clear_run (port : Fin 15) (again next : Fin 192)
    (hc : program again = clear port again next) (word : List Bool)
    (other : Fin 15 → List Bool) (v : Fin 3) :
    tick^[word.length+1] ⟨some again,v,Function.update other port word⟩ =
      ⟨some next,0,Function.update other port []⟩ := by
  induction word generalizing v with
  | nil => simp [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory]
  | cons bit word ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    cases bit
    · simpa [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory] using ih 1
    · simpa [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory] using ih 2

private theorem clear_accumulator (product : Bool)
    (a raw operand base pending exponent modulus context : List Bool) :
    tick^[a.length+1] (state (some (if product then 7 else 3)) a raw operand base pending exponent modulus context) =
      state (some (multiplyLabel product (BinaryModMultiply.copyLabel 0))) [] raw operand base pending exponent modulus context := by
  have h := clear_run 0 (if product then 7 else 3) (multiplyLabel product (BinaryModMultiply.copyLabel 0))
    (by cases product <;> rfl) a (state none [] raw operand base pending exponent modulus context).stk 0
  have hi : (⟨some (if product then 7 else 3),0,
      Function.update (state none [] raw operand base pending exponent modulus context).stk 0 a⟩ : Config) =
      state (some (if product then 7 else 3)) a raw operand base pending exponent modulus context := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : (⟨some (multiplyLabel product (BinaryModMultiply.copyLabel 0)),0,
      Function.update (state none [] raw operand base pending exponent modulus context).stk 0 []⟩ : Config) =
      state (some (multiplyLabel product (BinaryModMultiply.copyLabel 0))) [] raw operand base pending exponent modulus context := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rwa [hi,ho] at h

private theorem clear_operand (product : Bool)
    (a operand base pending exponent modulus context : List Bool) :
    tick^[operand.length+1] (state (some (if product then 9 else 5)) a [] operand base pending exponent modulus context) =
      state (some (if product then 2 else 6)) a [] [] base pending exponent modulus context := by
  have h := clear_run 10 (if product then 9 else 5) (if product then 2 else 6)
    (by cases product <;> rfl) operand (state none a [] [] base pending exponent modulus context).stk 0
  have hi : (⟨some (if product then 9 else 5),0,
      Function.update (state none a [] [] base pending exponent modulus context).stk 10 operand⟩ : Config) =
      state (some (if product then 9 else 5)) a [] operand base pending exponent modulus context := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : (⟨some (if product then 2 else 6),0,
      Function.update (state none a [] [] base pending exponent modulus context).stk 10 []⟩ : Config) =
      state (some (if product then 2 else 6)) a [] [] base pending exponent modulus context := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rwa [hi,ho] at h

private theorem multiply_run (product : Bool) (p a : Nat) (raw : List Bool) (ha : a < p)
    (base pending exponent context : List Bool) :
    ∃ used ≤ BinaryModMultiply.clock p raw.length,
      tick^[used] (state (some (multiplyLabel product (BinaryModMultiply.copyLabel 0))) [] raw a.bits base pending exponent p.bits context) =
        state (some (if product then 8 else 4)) ((a*bitsValue raw)%p).bits [] a.bits base pending exponent p.bits context 2 := by
  have inner := BinaryModMultiply.padded_run p a raw ha
  have hf := TM2StackFrame.run layout BinaryModMultiply.program (BinaryModMultiply.clock p raw.length)
    (BinaryModMultiply.start a.bits raw p.bits) ![base,pending,exponent,context]
  change (TM2ReturnLink.tick multiplyProgram)^[BinaryModMultiply.clock p raw.length] _ = _ at hf
  change (TM2ReturnLink.tick BinaryModMultiply.program)^[BinaryModMultiply.clock p raw.length] _ = _ at inner
  rw [inner] at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run multiplyProgram program (multiplyLabel product)
    (if product then 8 else 4) (multiply_code product) (BinaryModMultiply.clock p raw.length) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hi : TM2ReturnLink.embed (multiplyLabel product) (if product then 8 else 4)
      (TM2StackFrame.embed layout (BinaryModMultiply.start a.bits raw p.bits) ![base,pending,exponent,context]) =
      state (some (multiplyLabel product (BinaryModMultiply.copyLabel 0))) [] raw a.bits base pending exponent p.bits context := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed (multiplyLabel product) (if product then 8 else 4)
      (TM2StackFrame.embed layout (BinaryModMultiply.result ((a*bitsValue raw)%p).bits a.bits p.bits)
        ![base,pending,exponent,context]) =
      state (some (if product then 8 else 4)) ((a*bitsValue raw)%p).bits [] a.bits base pending exponent p.bits context 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hi,ho] at he⟩

private theorem copy_pair (product : Bool)
    (a base pending exponent modulus context : List Bool) :
    ∃ used ≤ (2*a.length+2)+(2*(if product then base else a).length+2),
      tick^[used] (state (some (copyLabel (if product then 3 else 1) 0)) a [] [] base pending exponent modulus context) =
      state (some (if product then 7 else 3)) a (if product then base else a) a base pending exponent modulus context := by
  cases product
  · obtain ⟨u,hu,he⟩ := copy_run 1 a [] [] base pending exponent modulus context
    obtain ⟨v,hv,hf⟩ := copy_run 2 a [] a base pending exponent modulus context
    exact ⟨v+u,by dsimp [copyWord] at hu hv ⊢; omega,sequence he hf⟩
  · obtain ⟨u,hu,he⟩ := copy_run 3 a [] [] base pending exponent modulus context
    obtain ⟨v,hv,hf⟩ := copy_run 4 a [] a base pending exponent modulus context
    exact ⟨v+u,by dsimp [copyWord] at hu hv ⊢; omega,sequence he hf⟩

private theorem guard_run (product : Bool)
    (a operand base pending exponent modulus context : List Bool) :
    tick^[1] (state (some (if product then 8 else 4)) a [] operand base pending exponent modulus context 2) =
      state (some (if product then 9 else 5)) a [] operand base pending exponent modulus context := by
  cases product <;> rfl

private theorem call_run (product : Bool) (p a base : Nat) (ha : a < p) (hb : base < p)
    (pending exponent context : List Bool) :
    ∃ used ≤ BinaryModMultiply.clock p p.size + 6*p.size+7,
      tick^[used] (state (some (copyLabel (if product then 3 else 1) 0)) a.bits [] [] base.bits pending exponent p.bits context) =
      state (some (if product then 2 else 6)) ((a*(if product then base else a))%p).bits [] [] base.bits pending exponent p.bits context := by
  obtain ⟨u,hu,hcopy⟩ := copy_pair product a.bits base.bits pending exponent p.bits context
  have hclear := clear_accumulator product a.bits (if product then base.bits else a.bits) a.bits base.bits pending exponent p.bits context
  obtain ⟨v,hv,hmul⟩ := multiply_run product p a (if product then base.bits else a.bits) ha base.bits pending exponent context
  have hg := guard_run product ((a*bitsValue (if product then base.bits else a.bits))%p).bits a.bits base.bits pending exponent p.bits context
  have hc := clear_operand product ((a*bitsValue (if product then base.bits else a.bits))%p).bits a.bits base.bits pending exponent p.bits context
  have haW : a.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size ha.le
  have hbW : base.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hb.le
  have hW : (if product then base.bits else a.bits).length ≤ p.size := by cases product <;> assumption
  have hm : BinaryModMultiply.clock p (if product then base.bits else a.bits).length ≤ BinaryModMultiply.clock p p.size := by
    unfold BinaryModMultiply.clock
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hW) _
  refine ⟨(a.bits.length+1)+(1+(v+((a.bits.length+1)+u))),?_,?_⟩
  · omega
  · have he := sequence hcopy (sequence hclear (sequence hmul (sequence hg hc)))
    have hvbits : bitsValue (if product then base.bits else a.bits) = if product then base else a := by
      cases product <;> simp [bitsValue_bits]
    simpa only [hvbits,Nat.add_assoc] using he

private theorem peek_nonempty (bit : Bool) (a base pending exponent modulus context : List Bool) :
    tick^[1] (state (some 2) a [] [] base (bit::pending) exponent modulus context) =
      state (some (copyLabel 1 0)) a [] [] base (bit::pending) exponent modulus context := by
  cases bit <;> rfl
private theorem pop_bit (bit : Bool) (a base pending exponent modulus context : List Bool) :
    tick^[1] (state (some 6) a [] [] base (bit::pending) exponent modulus context) =
      state (some (if bit then copyLabel 3 0 else 2)) a [] [] base pending exponent modulus context := by
  cases bit <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem finish (a base exponent modulus context : List Bool) :
    tick^[1] (state (some 2) a [] [] base [] exponent modulus context) = result a base exponent modulus context := rfl

private theorem one_bit (p base a : Nat) (bit : Bool) (pending exponent context : List Bool)
    (hp : 2 ≤ p) (hb : base < p) (ha : a < p) :
    ∃ used ≤ 2*BinaryModMultiply.clock p p.size+12*p.size+16,
      tick^[used] (state (some 2) a.bits [] [] base.bits (bit::pending) exponent p.bits context) =
      state (some 2) (BinaryModPowerArithmetic.step p base a bit).bits [] [] base.bits pending exponent p.bits context := by
  have hpeek := peek_nonempty bit a.bits base.bits pending exponent p.bits context
  obtain ⟨u,hu,hsquare⟩ := call_run false p a base ha hb (bit::pending) exponent context
  have hpop := pop_bit bit ((a*a)%p).bits base.bits pending exponent p.bits context
  have hs : (a*a)%p < p := Nat.mod_lt _ (by omega)
  cases bit
  · refine ⟨1+(u+1),by omega,?_⟩
    simpa [Nat.add_assoc,BinaryModPowerArithmetic.step] using sequence hpeek (sequence hsquare hpop)
  · obtain ⟨v,hv,hproduct⟩ := call_run true p ((a*a)%p) base hs hb pending exponent context
    refine ⟨v+(1+(u+1)),by omega,?_⟩
    simpa [Nat.add_assoc,BinaryModPowerArithmetic.step] using sequence hpeek (sequence hsquare (sequence hpop hproduct))

private theorem loop (p base : Nat) (hp : 2 ≤ p) (hb : base < p)
    (pending : List Bool) (a : Nat) (ha : a < p) (exponent context : List Bool) :
    ∃ used ≤ pending.length*(2*BinaryModMultiply.clock p p.size+12*p.size+16)+1,
      tick^[used] (state (some 2) a.bits [] [] base.bits pending exponent p.bits context) =
      result (pending.foldl (BinaryModPowerArithmetic.step p base) a).bits base.bits exponent p.bits context := by
  induction pending generalizing a with
  | nil => exact ⟨1,by simp,finish _ _ _ _ _⟩
  | cons bit pending ih =>
    obtain ⟨u,hu,he⟩ := one_bit p base a bit pending exponent context hp hb ha
    obtain ⟨v,hv,hf⟩ := ih (BinaryModPowerArithmetic.step p base a bit)
      (BinaryModPowerArithmetic.step_lt p base a bit (by omega))
    refine ⟨v+u,?_,sequence he hf⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Complete loaded execution; all work ports clear and all three retained words unchanged. -/
theorem run (p base : Nat) (raw context : List Bool) (hp : 2 ≤ p) (hx : base < p) :
    ∃ used ≤ clock p raw.length,
      tick^[used] (start base.bits raw p.bits context) =
      result ((base^bitsValue raw)%p).bits base.bits raw p.bits context := by
  obtain ⟨u,hu,he⟩ := prepare base.bits raw p.bits context
  obtain ⟨v,hv,hf⟩ := loop p base hp hx raw.reverse 1 (by omega) raw context
  have h := sequence he hf
  rw [BinaryModPowerArithmetic.fold_reverse_one p base raw hp] at h
  refine ⟨v+u,?_,h⟩
  simp only [List.length_reverse] at hv
  unfold clock
  omega

/-- The remaining fuel is spent only at the final halted configuration. -/
theorem padded_run (p base : Nat) (raw context : List Bool) (hp : 2 ≤ p) (hx : base < p) :
    tick^[clock p raw.length] (start base.bits raw p.bits context) =
      result ((base^bitsValue raw)%p).bits base.bits raw p.bits context := by
  obtain ⟨u,hu,he⟩ := run p base raw context hp hx
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) d

/-- A finite instruction audit, independent of operand values. -/
theorem local_cost (l : Fin 192) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Actual execution charge, derived from the instruction audit and checked run. -/
theorem charged (p base : Nat) (raw context : List Bool) (hp : 2 ≤ p) (hx : base < p) :
    ∃ charge ≤ 32*clock p raw.length,
      BitOracleMachine.run code (clock p raw.length) (start base.bits raw p.bits context) =
      pure (result ((base^bitsValue raw)%p).bits base.bits raw p.bits context,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock p raw.length) (start base.bits raw p.bits context)
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run code (clock p raw.length) (start base.bits raw p.bits context) =
    pure (tick^[clock p raw.length] (start base.bits raw p.bits context),charge) at he
  rw [he,padded_run p base raw context hp hx]

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.BinaryModPower
