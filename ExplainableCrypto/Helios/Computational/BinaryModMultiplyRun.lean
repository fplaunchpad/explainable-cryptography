import ExplainableCrypto.Helios.Computational.BinaryModMultiply
import ExplainableCrypto.Helios.Computational.BinaryModMultiplyArithmetic
import ExplainableCrypto.Helios.Computational.BinaryModAddMachineRun

namespace ExplainableCrypto.Helios.Computational.BinaryModMultiply
open Turing.TM2

private theorem prep_code (l : Fin 11) : program (prepLabel l) =
    TM2ReturnLink.redirect prepLabel 6 (coreProgram 0 l) := by fin_cases l <;> rfl
private theorem double_code (b : Bool) (l : Fin 11) : program (doubleLabel b l) =
    TM2ReturnLink.redirect (doubleLabel b) (toTemp b) (coreProgram 1 l) := by
  cases b <;> fin_cases l <;> rfl
private theorem add_code (l : Fin 42) : program (addLabel l) =
    TM2ReturnLink.redirect addLabel 7 (addProgram l) := by fin_cases l <;> rfl
private theorem copy_code (l : Fin 2) : program (copyLabel l) =
    TM2ReturnLink.redirect copyLabel (prepLabel 0) (copyProgram l) := by fin_cases l <;> rfl

/-- Live controller states explicitly expose every arithmetic and saved port. -/
def state (l : Option (Fin 86)) (a c out archive modulus raw pending x : List Bool)
    (v : Fin 3 := 0) : Config :=
  ⟨l,v,![a,c,[],archive,[],out,modulus,[],raw,pending,x]⟩

private theorem core_transfer (which : Fin 2) (labels : Fin 11 → Fin 86) (ret : Fin 86)
    (hcode : ∀ l, program (labels l) = TM2ReturnLink.redirect labels ret (coreProgram which l))
    (fuel : Nat) (initial final : BinarySubtractMachine.Config) (frame : Fin 5 → List Bool)
    (he : BinarySubtractMachine.tick^[fuel] initial = final) (hh : final.l = none) :
    ∃ used ≤ fuel, tick^[used] (TM2ReturnLink.embed labels ret (corePresent which initial frame)) =
      TM2ReturnLink.embed labels ret (corePresent which final frame) := by
  have hs : (TM2ReturnLink.tick (coreProgram which))^[fuel] (corePresent which initial frame) =
      corePresent which final frame := by
    rw [coreProgram,corePresent,TM2FiniteCoordinates.run,TM2StackFrame.run]
    change _ = TM2FiniteCoordinates.present _ _ _ (TM2StackFrame.embed _ final frame)
    rw [show (TM2ReturnLink.tick BinarySubtractMachine.program)^[fuel] initial = final from he]
  obtain ⟨u,hu,hr⟩ := TM2ReturnLink.run (coreProgram which) program labels ret hcode fuel
    (corePresent which initial frame) (by rw [hs]; simp [corePresent,TM2FiniteCoordinates.present,TM2StackFrame.embed,hh])
  rw [hs] at hr
  exact ⟨u,hu,hr⟩

private theorem load_modulus (p x : Nat) (raw : List Bool) :
    ∃ used ≤ 2*p.size+2, tick^[used] (start x.bits raw p.bits) =
      state (some (prepLabel 0)) p.bits [] [] [] p.bits raw [] x.bits := by
  let inner := BinaryModAddMachine.copyPresent 1 (BitCopyMachine.config (some false) p.bits [] []) (fun _ => [])
  let final := BinaryModAddMachine.copyPresent 1 (BitCopyMachine.config none p.bits p.bits []) (fun _ => [])
  have hi : (TM2ReturnLink.tick (BinaryModAddMachine.copyProgram 1))^[2*p.bits.length+2] inner = final := by
    dsimp only [inner]
    rw [BinaryModAddMachine.copyProgram,BinaryModAddMachine.copyPresent,
      TM2FiniteCoordinates.run,TM2StackFrame.run]
    rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*p.bits.length+2]
      (BitCopyMachine.config (some false) p.bits [] []) =
      BitCopyMachine.config none p.bits (p.bits++[]) [] from BitCopyMachine.run _ _ none]
    simp only [List.append_nil]
    rfl
  have hf := TM2StackFrame.run layout (BinaryModAddMachine.copyProgram 1) (2*p.bits.length+2)
    inner ![raw,[],x.bits]
  rw [hi] at hf
  change (TM2ReturnLink.tick copyProgram)^[2*p.bits.length+2]
    (TM2StackFrame.embed layout inner ![raw,[],x.bits]) =
      TM2StackFrame.embed layout final ![raw,[],x.bits] at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run copyProgram program copyLabel (prepLabel 0) copy_code
    (2*p.bits.length+2) (TM2StackFrame.embed layout inner ![raw,[],x.bits]) (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed copyLabel (prepLabel 0)
      (TM2StackFrame.embed layout inner ![raw,[],x.bits]) = start x.bits raw p.bits := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed copyLabel (prepLabel 0)
      (TM2StackFrame.embed layout final ![raw,[],x.bits]) =
      state (some (prepLabel 0)) p.bits [] [] [] p.bits raw [] x.bits := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  refine ⟨u,?_,?_⟩
  · simpa only [← Nat.size_eq_bits_len] using hu
  · simpa only [hs,ht,tick] using he

/-- The multiplier derives its complement through actual copied-modulus
subtraction. It does not receive c=p-x as an entry premise. -/
theorem prepare (p x : Nat) (hx : x < p) (raw : List Bool) :
    ∃ used ≤ 8*p.size+8, tick^[used] (start x.bits raw p.bits) =
      state (some 0) [] (p-x).bits [] [] p.bits raw [] x.bits := by
  obtain ⟨u,hu,hload⟩ := load_modulus p x raw
  obtain ⟨v,hv,hsub⟩ := BinarySubtractMachine.run p.bits x.bits
  simp only [bitsValue_bits,if_pos hx.le,decide_eq_true hx.le] at hsub
  obtain ⟨v',hv',hcall⟩ := core_transfer 0 prepLabel 6 prep_code v _ _
    ![[],p.bits,[],raw,[]] hsub rfl
  have hs : TM2ReturnLink.embed prepLabel 6
      (corePresent 0 (BinarySubtractMachine.state (some (.scan false)) p.bits x.bits [] [] [] [])
        ![[],p.bits,[],raw,[]]) =
      state (some (prepLabel 0)) p.bits [] [] [] p.bits raw [] x.bits := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed prepLabel 6
      (corePresent 0 (BinarySubtractMachine.state none [] x.bits [] [] [] (p-x).bits (some true))
        ![[],p.bits,[],raw,[]]) =
      state (some 6) [] (p-x).bits [] [] p.bits raw [] x.bits 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hs,ht] at hcall
  have hg : tick (state (some 6) [] (p-x).bits [] [] p.bits raw [] x.bits 2) =
      state (some 0) [] (p-x).bits [] [] p.bits raw [] x.bits := rfl
  refine ⟨1+(v'+u),?_,?_⟩
  · have hw := Nat.size_le_size hx.le
    have hb : v ≤ 3*(p.size+x.size)+5 := by simpa only [Nat.size_eq_bits_len] using hv
    omega
  · rw [Function.iterate_add_apply,Function.iterate_add_apply,hload,hcall]
    exact hg


private def moveState (source dest : Fin 11) (label : Fin 86)
    (word acc : List Bool) (other : Fin 11 → List Bool) (v : Fin 3) : Config :=
  ⟨some label,v,Function.update (Function.update other dest acc) source word⟩

private theorem move_step (source dest : Fin 11) (hne : source ≠ dest)
    (again next : Fin 86) (hc : program again = move source dest again next)
    (b : Bool) (word acc : List Bool) (other : Fin 11 → List Bool) (v : Fin 3) :
    tick (moveState source dest again (b::word) acc other v) =
      moveState source dest again word (b::acc) other (BinaryModuloCode.memory (some b)) := by
  cases b <;>
    simp [tick,TM2ReturnLink.tick,step,moveState,hc,move,stepAux,
      BinaryModuloCode.memory,Function.update,Ne.symm hne]
  all_goals
    funext k
    by_cases hs : k = source <;> by_cases hd : k = dest <;>
      simp_all [Function.update]

private theorem move_run (source dest : Fin 11) (hne : source ≠ dest)
    (again next : Fin 86) (hc : program again = move source dest again next)
    (word acc : List Bool) (other : Fin 11 → List Bool) (v : Fin 3) :
    tick^[word.length+1] (moveState source dest again word acc other v) =
      moveState source dest next [] (word.reverse++acc) other 0 := by
  induction word generalizing acc v with
  | nil =>
    simp [tick,TM2ReturnLink.tick,moveState,hc,move,enter,stepAux,BinaryModuloCode.memory]
  | cons b word ih =>
    rw [List.length_cons,Function.iterate_succ_apply,move_step source dest hne again next hc,ih]
    simp [List.reverse_cons,List.append_assoc]

private theorem reverse_input (a c p raw pending x : List Bool) (v : Fin 3) :
    tick^[raw.length+1] (state (some 0) a c [] [] p raw pending x v) =
      state (some 1) a c [] [] p [] (raw.reverse++pending) x := by
  have h := move_run 8 9 (by decide) 0 1 rfl raw pending
    (state none a c [] [] p [] [] x).stk v
  have hi : moveState 8 9 0 raw pending (state none a c [] [] p [] [] x).stk v =
      state (some 0) a c [] [] p raw pending x v := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have hf : moveState 8 9 1 [] (raw.reverse++pending) (state none a c [] [] p [] [] x).stk 0 =
      state (some 1) a c [] [] p [] (raw.reverse++pending) x := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  simpa only [hi,hf] using h

private theorem sequence {a b c : Config} {n k : Nat}
    (h : tick^[n] a = b) (h' : tick^[k] b = c) : tick^[k+n] a = c := by
  rw [Function.iterate_add_apply,h,h']

private theorem double_run (p r : Nat) (hr : r < p) (b : Bool)
    (c raw pending x : List Bool) :
    ∃ used ≤ 6*p.size+9,
      tick^[used] (state (some (doubleLabel b 4)) r.bits c [] [] p.bits raw pending x) =
        state (some (toTemp b)) [] c ((2*r)%p).bits [] p.bits raw pending x
          (BinaryModuloCode.memory (some (decide (p ≤ 2*r)))) := by
  obtain ⟨u,hu,he⟩ := BinarySubtractMachine.remainder_step r p false hr
  simp only [Nat.bit_val,Bool.toNat_false,Nat.add_zero] at he
  obtain ⟨v,hv,hcall⟩ := core_transfer 1 (doubleLabel b) (toTemp b) (double_code b) u _ _
    ![c,[],raw,pending,x] he rfl
  have hi : TM2ReturnLink.embed (doubleLabel b) (toTemp b)
      (corePresent 1 (BinarySubtractMachine.state (some (.shift false)) r.bits p.bits [] [] [] [])
        ![c,[],raw,pending,x]) =
      state (some (doubleLabel b 4)) r.bits c [] [] p.bits raw pending x := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed (doubleLabel b) (toTemp b)
      (corePresent 1 (BinarySubtractMachine.state none [] p.bits [] [] [] ((2*r)%p).bits
        (some (decide (p ≤ 2*r)))) ![c,[],raw,pending,x]) =
      state (some (toTemp b)) [] c ((2*r)%p).bits [] p.bits raw pending x
        (BinaryModuloCode.memory (some (decide (p ≤ 2*r)))) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨v,hv.trans hu,by rwa [hi,ho] at hcall⟩

private theorem move_double (b : Bool) (word c p pending x : List Bool) (v : Fin 3) :
    tick^[2*word.length+2] (state (some (toTemp b)) [] c word [] p [] pending x v) =
      state (some (if b then addLabel 5 else 1)) word c [] [] p [] pending x := by
  have first := move_run 5 3 (by decide) (toTemp b) (toLeft b)
    (by cases b <;> rfl) word [] (state none [] c [] [] p [] pending x).stk v
  have hi : moveState 5 3 (toTemp b) word [] (state none [] c [] [] p [] pending x).stk v =
      state (some (toTemp b)) [] c word [] p [] pending x v := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have hm : moveState 5 3 (toLeft b) [] (word.reverse++[]) (state none [] c [] [] p [] pending x).stk 0 =
      state (some (toLeft b)) [] c [] word.reverse p [] pending x := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> simp only [List.append_nil] <;> rfl
  rw [hi,hm] at first
  have second := move_run 3 0 (by decide) (toLeft b) (if b then addLabel 5 else 1)
    (by cases b <;> rfl) word.reverse [] (state none [] c [] [] p [] pending x).stk 0
  have hi' : moveState 3 0 (toLeft b) word.reverse [] (state none [] c [] [] p [] pending x).stk 0 =
      state (some (toLeft b)) [] c [] word.reverse p [] pending x := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : moveState 3 0 (if b then addLabel 5 else 1) [] (word.reverse.reverse++[])
      (state none [] c [] [] p [] pending x).stk 0 =
      state (some (if b then addLabel 5 else 1)) word c [] [] p [] pending x := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> simp only [List.reverse_reverse,List.append_nil] <;> rfl
  rw [hi',ho,List.length_reverse] at second
  simpa only [two_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using sequence first second

private theorem add_run (p x r : Nat) (hx : x < p) (hr : r < p) (pending : List Bool) :
    ∃ used ≤ 26*p.size+25,
      tick^[used] (state (some (addLabel 5)) r.bits (p-x).bits [] [] p.bits [] pending x.bits) =
        state (some 1) ((r+x)%p).bits (p-x).bits [] [] p.bits [] pending x.bits := by
  have inner := BinaryModAddMachine.run p x r hx hr
  have hf := TM2StackFrame.run layout BinaryModAddMachine.program (BinaryModAddMachine.clock p)
    (BinaryModAddMachine.start r.bits (p-x).bits p.bits) ![[],pending,x.bits]
  change (TM2ReturnLink.tick addProgram)^[BinaryModAddMachine.clock p] _ = _ at hf
  change (TM2ReturnLink.tick BinaryModAddMachine.program)^[BinaryModAddMachine.clock p] _ = _ at inner
  rw [inner] at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run addProgram program addLabel 7 add_code
    (BinaryModAddMachine.clock p) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hi : TM2ReturnLink.embed addLabel 7 (TM2StackFrame.embed layout
      (BinaryModAddMachine.start r.bits (p-x).bits p.bits) ![[],pending,x.bits]) =
      state (some (addLabel 5)) r.bits (p-x).bits [] [] p.bits [] pending x.bits := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed addLabel 7 (TM2StackFrame.embed layout
      (BinaryModAddMachine.result ((r+x)%p).bits (p-x).bits p.bits) ![[],pending,x.bits]) =
      state (some 7) ((r+x)%p).bits (p-x).bits [] [] p.bits [] pending x.bits 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hi,ho] at he
  have gate : tick^[1] (state (some 7) ((r+x)%p).bits (p-x).bits [] [] p.bits [] pending x.bits 2) =
      state (some 1) ((r+x)%p).bits (p-x).bits [] [] p.bits [] pending x.bits := rfl
  refine ⟨1+u,?_,sequence he gate⟩
  unfold BinaryModAddMachine.clock at hu
  omega

private theorem clear_complement (a c p x : List Bool) (v : Fin 3) :
    tick^[c.length+1] (state (some 8) a c [] [] p [] [] x v) = result a x p := by
  induction c generalizing v with
  | nil =>
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  | cons b c ih =>
    have hs : tick (state (some 8) a (b::c) [] [] p [] [] x v) =
        state (some 8) a c [] [] p [] [] x (if b then 2 else 1) := by
      cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      all_goals congr 1; funext k; fin_cases k <;> rfl
    rw [List.length_cons,Function.iterate_succ_apply,hs,ih]

private theorem finish (a c p x : List Bool) :
    tick^[c.length+2] (state (some 1) a c [] [] p [] [] x) = result a x p := by
  have hs : tick (state (some 1) a c [] [] p [] [] x) =
      state (some 8) a c [] [] p [] [] x := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [Function.iterate_succ_apply,hs]
  exact clear_complement a c p x 0

private theorem read_step (b : Bool) (a c p pending x : List Bool) :
    tick^[1] (state (some 1) a c [] [] p [] (b::pending) x) =
      state (some (doubleLabel b 4)) a c [] [] p [] pending x := by
  cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl

private theorem one_bit (p x r : Nat) (hx : x < p) (hr : r < p)
    (b : Bool) (pending : List Bool) :
    ∃ used ≤ 34*p.size+37,
      tick^[used] (state (some 1) r.bits (p-x).bits [] [] p.bits [] (b::pending) x.bits) =
        state (some 1) (BinaryModMultiplyArithmetic.step p x r b).bits
          (p-x).bits [] [] p.bits [] pending x.bits := by
  have hread := read_step b r.bits (p-x).bits p.bits pending x.bits
  obtain ⟨u,hu,hd⟩ := double_run p r hr b (p-x).bits [] pending x.bits
  have hm := move_double b ((2*r)%p).bits (p-x).bits p.bits pending x.bits
    (BinaryModuloCode.memory (some (decide (p ≤ 2*r))))
  have hr' : (2*r)%p < p := Nat.mod_lt _ (by omega)
  have hw := Nat.size_le_size hr'.le
  cases b
  · have he := sequence hread (sequence hd hm)
    refine ⟨(2*((2*r)%p).bits.length+2)+u+1,?_,?_⟩
    · simp only [Nat.size_eq_bits_len]; omega
    · simpa [BinaryModMultiplyArithmetic.step] using he
  · obtain ⟨v,hv,ha⟩ := add_run p x ((2*r)%p) hx hr' pending
    have he := sequence hread (sequence hd (sequence hm ha))
    refine ⟨(v+(2*((2*r)%p).bits.length+2))+u+1,?_,?_⟩
    · simp only [Nat.size_eq_bits_len]; omega
    · simpa [BinaryModMultiplyArithmetic.step] using he

private theorem loop (p x : Nat) (hx : x < p) (pending : List Bool) (r : Nat) (hr : r < p) :
    ∃ used ≤ pending.length*(34*p.size+37)+(p-x).bits.length+2,
      tick^[used] (state (some 1) r.bits (p-x).bits [] [] p.bits [] pending x.bits) =
        result (pending.foldl (BinaryModMultiplyArithmetic.step p x) r).bits x.bits p.bits := by
  induction pending generalizing r with
  | nil =>
    exact ⟨(p-x).bits.length+2,by simp,finish r.bits (p-x).bits p.bits x.bits⟩
  | cons b pending ih =>
    obtain ⟨u,hu,he⟩ := one_bit p x r hx hr b pending
    obtain ⟨v,hv,hf⟩ := ih (BinaryModMultiplyArithmetic.step p x r b)
      (BinaryModMultiplyArithmetic.step_lt p x r b (by omega))
    refine ⟨v+u,?_,sequence he hf⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Complete loaded multiplication derives the complement, reverses the actual
multiplier word and executes every double/add iteration and final cleanup.
The input multiplicand and modulus are retained in the full final state. -/
theorem run (p x : Nat) (raw : List Bool) (hx : x < p) :
    ∃ used ≤ clock p raw.length,
      tick^[used] (start x.bits raw p.bits) =
        result ((x*bitsValue raw)%p).bits x.bits p.bits := by
  obtain ⟨u,hu,hprep⟩ := prepare p x hx raw
  have hreverse := reverse_input [] (p-x).bits p.bits raw [] x.bits 0
  simp only [List.append_nil] at hreverse
  obtain ⟨v,hv,hloop⟩ := loop p x hx raw.reverse 0 (by omega)
  have he := sequence hprep (sequence hreverse hloop)
  have answer := BinaryModMultiplyArithmetic.fold_reverse_zero p x raw
  refine ⟨_,?_,he.trans (congrArg (fun n => result n.bits x.bits p.bits) answer)⟩
  have hw := Nat.size_le_size (Nat.sub_le p x)
  simp only [List.length_reverse,Nat.size_eq_bits_len] at hv
  have expand : raw.length*(34*p.size+38) = raw.length*(34*p.size+37)+raw.length := by
    rw [show 34*p.size+38 = (34*p.size+37)+1 by omega,Nat.mul_add,Nat.mul_one]
  unfold clock
  rw [expand]
  omega

/-- Padding is applied only after the multiplier's actual final halt. -/
theorem padded_run (p x : Nat) (raw : List Bool) (hx : x < p) :
    tick^[clock p raw.length] (start x.bits raw p.bits) =
      result ((x*bitsValue raw)%p).bits x.bits p.bits := by
  obtain ⟨used,hu,he⟩ := run p x raw hx
  obtain ⟨extra,hclock⟩ := Nat.exists_eq_add_of_le hu
  have hh : tick (result ((x*bitsValue raw)%p).bits x.bits p.bits) =
      result ((x*bitsValue raw)%p).bits x.bits p.bits := rfl
  rw [hclock,Nat.add_comm used extra,Function.iterate_add_apply,he]
  exact Function.iterate_fixed hh extra

/-- Every actual finite-control instruction has a constant local cost. -/
theorem local_cost (label : Fin 86) : BitOracleMachine.localCost (program label) ≤ 32 := by
  fin_cases label <;> decide +kernel

/-- The raw charged run is derived from the executed program and full clock. -/
theorem charged (p x : Nat) (raw : List Bool) (hx : x < p) :
    ∃ charge ≤ 32*clock p raw.length,
      BitOracleMachine.run code (clock p raw.length) (start x.bits raw p.bits) =
        pure (result ((x*bitsValue raw)%p).bits x.bits p.bits,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock p raw.length) (start x.bits raw p.bits)
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run code (clock p raw.length) (start x.bits raw p.bits) =
    pure (tick^[clock p raw.length] (start x.bits raw p.bits),charge) at he
  rw [he,padded_run p x raw hx]

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
#print axioms prepare
end ExplainableCrypto.Helios.Computational.BinaryModMultiply
