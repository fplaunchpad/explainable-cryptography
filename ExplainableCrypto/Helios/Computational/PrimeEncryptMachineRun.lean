import ExplainableCrypto.Helios.Computational.PrimeEncryptMachine
import ExplainableCrypto.Helios.Computational.BinaryModPowerRun

/-! Complete resident encryption execution. The controller derives every frame,
copy, return and width condition from the retained canonical operands. -/
namespace ExplainableCrypto.Helios.Computational.PrimeEncryptMachine
open Turing.TM2
set_option maxRecDepth 16384

private theorem copy_code (which : Fin 5) (l : Fin 2) : program (copyLabel which l) =
    TM2ReturnLink.redirect (copyLabel which) (copyReturn which) (copyProgram which l) := by
  fin_cases which <;> fin_cases l <;> rfl
private theorem power_code (which : Fin 2) (l : Fin 192) : program (powerLabel which l) =
    TM2ReturnLink.redirect (powerLabel which) (powerReturn which) (powerProgram l) := by
  fin_cases which <;> fin_cases l <;> rfl
private theorem multiply_code (l : Fin 86) : program (multiplyLabel l) =
    TM2ReturnLink.redirect multiplyLabel 6 (multiplyProgram l) := by
  fin_cases l <;> rfl

private def state (l : Option (Fin 490))
    (a raw operand base nonce modulus context pk g alpha : List Bool) (vote : Bool)
    (v : Fin 3 := 0) : Config :=
  ⟨l,v,![a,[],[],[],[],[],modulus,[],raw,[],operand,base,[],nonce,context,pk,g,alpha,[vote]]⟩

private theorem sequence {a b c : Config} {n k : Nat}
    (h : tick^[n] a = b) (h' : tick^[k] b = c) : tick^[k+n] a = c := by
  rw [Function.iterate_add_apply,h,h']

private def copyWord (which : Fin 5) (a pk g : List Bool) := ![g,a,pk,a,g] which
private def copyFrame (which : Fin 5)
    (a raw operand base nonce modulus context pk g alpha : List Bool) (vote : Bool) :
    Fin 11 → List Bool :=
  ![![a,modulus,raw,[],operand,[],nonce,context,pk,alpha,[vote]],
    ![modulus,raw,[],operand,base,[],nonce,context,pk,g,[vote]],
    ![a,modulus,raw,[],operand,[],nonce,context,g,alpha,[vote]],
    ![modulus,raw,[],base,[],nonce,context,pk,g,alpha,[vote]],
    ![a,modulus,[],operand,base,[],nonce,context,pk,alpha,[vote]]] which

private theorem copy_run (which : Fin 5)
    (a raw operand base nonce modulus context pk g alpha : List Bool) (vote : Bool) :
    ∃ used ≤ 2*(copyWord which a pk g).length+2,
      tick^[used] (state (some (copyLabel which 0)) a (![raw,raw,raw,raw,[]] which)
        (![operand,operand,operand,[],operand] which) (![[],base,[],base,base] which)
        nonce modulus context pk g (![alpha,[],alpha,alpha,alpha] which) vote) =
      state (some (copyReturn which)) a (![raw,raw,raw,raw,g] which)
        (![operand,operand,operand,a,operand] which) (![g,base,pk,base,base] which)
        nonce modulus context pk g (![alpha,a,alpha,alpha,alpha] which) vote := by
  let word := copyWord which a pk g
  let frame := copyFrame which a raw operand base nonce modulus context pk g alpha vote
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
      state (some (copyLabel which 0)) a (![raw,raw,raw,raw,[]] which)
        (![operand,operand,operand,[],operand] which) (![[],base,[],base,base] which)
        nonce modulus context pk g (![alpha,[],alpha,alpha,alpha] which) vote := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed (copyLabel which) (copyReturn which)
      (TM2StackFrame.embed (copyLayout which) final frame) =
      state (some (copyReturn which)) a (![raw,raw,raw,raw,g] which)
        (![operand,operand,operand,a,operand] which) (![g,base,pk,base,base] which)
        nonce modulus context pk g (![alpha,a,alpha,alpha,alpha] which) vote := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

private theorem clear_run (port : Fin 19) (again next : Fin 490)
    (hc : program again = clear port again next) (word : List Bool)
    (other : Fin 19 → List Bool) (v : Fin 3) :
    tick^[word.length+1] ⟨some again,v,Function.update other port word⟩ =
      ⟨some next,0,Function.update other port []⟩ := by
  induction word generalizing v with
  | nil => simp [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory]
  | cons bit word ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    cases bit
    · simpa [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory] using ih 1
    · simpa [tick,TM2ReturnLink.tick,step,hc,clear,enter,stepAux,BinaryModuloCode.memory] using ih 2

private def clearWord (which : Fin 5) (a operand base : List Bool) := ![a,base,a,operand,base] which
private def clearLabel (which : Fin 5) : Fin 490 := ![1,2,5,7,8] which
private def clearNext (which : Fin 5) : Fin 490 :=
  ![2,copyLabel 2 0,multiplyLabel (BinaryModMultiply.copyLabel 0),8,9] which
private def clearPort (which : Fin 5) : Fin 19 := ![0,11,0,10,11] which

private theorem clear_state (which : Fin 5)
    (a raw operand base nonce modulus context pk g alpha : List Bool) (vote : Bool) :
    tick^[(clearWord which a operand base).length+1]
      (state (some (clearLabel which)) a raw operand base nonce modulus context pk g alpha vote) =
      state (some (clearNext which)) (![[],a,[],a,a] which) raw
        (![operand,operand,operand,[],operand] which) (![base,[],base,base,[]] which)
        nonce modulus context pk g alpha vote := by
  have h := clear_run (clearPort which) (clearLabel which) (clearNext which)
    (by fin_cases which <;> rfl) (clearWord which a operand base)
    (state none a raw operand base nonce modulus context pk g alpha vote).stk 0
  have hi : (⟨some (clearLabel which),0,
      Function.update (state none a raw operand base nonce modulus context pk g alpha vote).stk
        (clearPort which) (clearWord which a operand base)⟩ : Config) =
      state (some (clearLabel which)) a raw operand base nonce modulus context pk g alpha vote := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ho : (⟨some (clearNext which),0,
      Function.update (state none a raw operand base nonce modulus context pk g alpha vote).stk
        (clearPort which) []⟩ : Config) =
      state (some (clearNext which)) (![[],a,[],a,a] which) raw
        (![operand,operand,operand,[],operand] which) (![base,[],base,base,[]] which)
        nonce modulus context pk g alpha vote := by
    fin_cases which <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  rwa [hi,ho] at h

private theorem power_run (which : Fin 2) (p base : Nat) (raw context pk g alpha : List Bool)
    (vote : Bool) (hp : 2 ≤ p) (hb : base < p) :
    ∃ used ≤ BinaryModPower.clock p raw.length,
      tick^[used] (state (some (powerLabel which (BinaryModPower.copyLabel 0 0)))
        [] [] [] base.bits raw p.bits context pk g alpha vote) =
      state (some (powerReturn which)) ((base^bitsValue raw)%p).bits [] [] base.bits raw p.bits context pk g alpha vote 2 := by
  have inner := BinaryModPower.padded_run p base raw context hp hb
  have hf := TM2StackFrame.run powerLayout BinaryModPower.program (BinaryModPower.clock p raw.length)
    (BinaryModPower.start base.bits raw p.bits context) ![pk,g,alpha,[vote]]
  change (TM2ReturnLink.tick powerProgram)^[BinaryModPower.clock p raw.length] _ = _ at hf
  change (TM2ReturnLink.tick BinaryModPower.program)^[BinaryModPower.clock p raw.length] _ = _ at inner
  rw [inner] at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run powerProgram program (powerLabel which)
    (powerReturn which) (power_code which) (BinaryModPower.clock p raw.length) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hi : TM2ReturnLink.embed (powerLabel which) (powerReturn which)
      (TM2StackFrame.embed powerLayout (BinaryModPower.start base.bits raw p.bits context) ![pk,g,alpha,[vote]]) =
      state (some (powerLabel which (BinaryModPower.copyLabel 0 0)))
        [] [] [] base.bits raw p.bits context pk g alpha vote := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed (powerLabel which) (powerReturn which)
      (TM2StackFrame.embed powerLayout
        (BinaryModPower.result ((base^bitsValue raw)%p).bits base.bits raw p.bits context) ![pk,g,alpha,[vote]]) =
      state (some (powerReturn which)) ((base^bitsValue raw)%p).bits [] [] base.bits raw p.bits context pk g alpha vote 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hi,ho] at he⟩

private theorem multiply_run (p a : Nat) (raw base nonce context pk g alpha : List Bool)
    (vote : Bool) (ha : a < p) :
    ∃ used ≤ BinaryModMultiply.clock p raw.length,
      tick^[used] (state (some (multiplyLabel (BinaryModMultiply.copyLabel 0)))
        [] raw a.bits base nonce p.bits context pk g alpha vote) =
      state (some 6) ((a*bitsValue raw)%p).bits [] a.bits base nonce p.bits context pk g alpha vote 2 := by
  have inner := BinaryModMultiply.padded_run p a raw ha
  have hf := TM2StackFrame.run multiplyLayout BinaryModMultiply.program (BinaryModMultiply.clock p raw.length)
    (BinaryModMultiply.start a.bits raw p.bits) ![base,[],nonce,context,pk,g,alpha,[vote]]
  change (TM2ReturnLink.tick multiplyProgram)^[BinaryModMultiply.clock p raw.length] _ = _ at hf
  change (TM2ReturnLink.tick BinaryModMultiply.program)^[BinaryModMultiply.clock p raw.length] _ = _ at inner
  rw [inner] at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run multiplyProgram program multiplyLabel
    6 multiply_code (BinaryModMultiply.clock p raw.length) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hi : TM2ReturnLink.embed multiplyLabel 6
      (TM2StackFrame.embed multiplyLayout (BinaryModMultiply.start a.bits raw p.bits)
        ![base,[],nonce,context,pk,g,alpha,[vote]]) =
      state (some (multiplyLabel (BinaryModMultiply.copyLabel 0)))
        [] raw a.bits base nonce p.bits context pk g alpha vote := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : TM2ReturnLink.embed multiplyLabel 6
      (TM2StackFrame.embed multiplyLayout (BinaryModMultiply.result ((a*bitsValue raw)%p).bits a.bits p.bits)
        ![base,[],nonce,context,pk,g,alpha,[vote]]) =
      state (some 6) ((a*bitsValue raw)%p).bits [] a.bits base nonce p.bits context pk g alpha vote 2 := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hi,ho] at he⟩

private theorem guard_run (which : Fin 3)
    (a raw operand base nonce modulus context pk g alpha : List Bool) (vote : Bool) :
    tick^[1] (state (some (![0,3,6] which)) a raw operand base nonce modulus context pk g alpha vote 2) =
      state (some (![copyLabel 1 0,4,7] which)) a raw operand base nonce modulus context pk g alpha vote := by
  fin_cases which <;> rfl

private theorem two_powers (p g pk : Nat) (raw context : List Bool) (vote : Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    ∃ used ≤ 2*BinaryModPower.clock p raw.length+8*p.size+10,
      tick^[used] (start g.bits pk.bits raw p.bits context vote) =
      state (some 4) ((pk^bitsValue raw)%p).bits [] [] pk.bits raw p.bits context pk.bits g.bits
        ((g^bitsValue raw)%p).bits vote := by
  let alpha := (g^bitsValue raw)%p
  let beta := (pk^bitsValue raw)%p
  obtain ⟨u,hu,hgcopy⟩ := copy_run 0 [] [] [] [] raw p.bits context pk.bits g.bits [] vote
  obtain ⟨v,hv,hgpow⟩ := power_run 0 p g raw context pk.bits g.bits [] vote hp hg
  have hgret := guard_run 0 alpha.bits [] [] g.bits raw p.bits context pk.bits g.bits [] vote
  obtain ⟨w,hw,hacopy⟩ := copy_run 1 alpha.bits [] [] g.bits raw p.bits context pk.bits g.bits [] vote
  have haclear := clear_state 0 alpha.bits [] [] g.bits raw p.bits context pk.bits g.bits alpha.bits vote
  have hgclear := clear_state 1 [] [] [] g.bits raw p.bits context pk.bits g.bits alpha.bits vote
  obtain ⟨z,hz,hpkcopy⟩ := copy_run 2 [] [] [] [] raw p.bits context pk.bits g.bits alpha.bits vote
  obtain ⟨t,ht,hpkpow⟩ := power_run 1 p pk raw context pk.bits g.bits alpha.bits vote hp hpk
  have hpkret := guard_run 1 beta.bits [] [] pk.bits raw p.bits context pk.bits g.bits alpha.bits vote
  have h := sequence hgcopy (sequence hgpow (sequence hgret (sequence hacopy
    (sequence haclear (sequence hgclear (sequence hpkcopy (sequence hpkpow hpkret)))))))
  have hgw : g.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hg.le
  have hpkw : pk.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hpk.le
  have haw : alpha.bits.length ≤ p.size := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.mod_lt (g^bitsValue raw) (by omega : 0 < p)).le
  refine ⟨1+(t+(z+((g.bits.length+1)+((alpha.bits.length+1)+(w+(1+(v+u))))))),?_,?_⟩
  · change u ≤ 2*g.bits.length+2 at hu
    change w ≤ 2*alpha.bits.length+2 at hw
    change z ≤ 2*pk.bits.length+2 at hz
    omega
  · simpa [clearWord,Nat.add_assoc,state,start,alpha,beta] using h

private theorem peek_vote (a base nonce modulus context pk g alpha : List Bool) (vote : Bool) :
    tick^[1] (state (some 4) a [] [] base nonce modulus context pk g alpha vote) =
      state (some (if vote then copyLabel 3 0 else 8)) a [] [] base nonce modulus context pk g alpha vote := by
  cases vote <;> rfl
private theorem halt_run (a nonce modulus context pk g alpha : List Bool) (vote : Bool) :
    tick^[1] (state (some 9) a [] [] [] nonce modulus context pk g alpha vote) =
      result alpha a g pk nonce modulus context vote := rfl

private theorem finish_true (p a g pk : Nat) (raw context alpha : List Bool)
    (ha : a < p) (hg : g < p) (hpk : pk < p) :
    ∃ used ≤ BinaryModMultiply.clock p p.size+7*p.size+10,
      tick^[used] (state (some 4) a.bits [] [] pk.bits raw p.bits context pk.bits g.bits alpha true) =
      result alpha ((a*g)%p).bits g.bits pk.bits raw p.bits context true := by
  have hpeek := peek_vote a.bits pk.bits raw p.bits context pk.bits g.bits alpha true
  obtain ⟨u,hu,hcopya⟩ := copy_run 3 a.bits [] [] pk.bits raw p.bits context pk.bits g.bits alpha true
  obtain ⟨v,hv,hcopyg⟩ := copy_run 4 a.bits [] a.bits pk.bits raw p.bits context pk.bits g.bits alpha true
  have hclear := clear_state 2 a.bits g.bits a.bits pk.bits raw p.bits context pk.bits g.bits alpha true
  obtain ⟨w,hw,hmul⟩ := multiply_run p a g.bits pk.bits raw context pk.bits g.bits alpha true ha
  simp only [bitsValue_bits] at hmul
  have hguard := guard_run 2 ((a*g)%p).bits [] a.bits pk.bits raw p.bits context pk.bits g.bits alpha true
  have hcleara := clear_state 3 ((a*g)%p).bits [] a.bits pk.bits raw p.bits context pk.bits g.bits alpha true
  have hclearpk := clear_state 4 ((a*g)%p).bits [] [] pk.bits raw p.bits context pk.bits g.bits alpha true
  have hhalt := halt_run ((a*g)%p).bits raw p.bits context pk.bits g.bits alpha true
  have h := sequence hpeek (sequence hcopya (sequence hcopyg (sequence hclear
    (sequence hmul (sequence hguard (sequence hcleara (sequence hclearpk hhalt)))))))
  have haw : a.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size ha.le
  have hgw : g.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hg.le
  have hpkw : pk.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hpk.le
  have hclock : BinaryModMultiply.clock p g.bits.length ≤ BinaryModMultiply.clock p p.size := by
    unfold BinaryModMultiply.clock
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hgw) _
  refine ⟨1+((pk.bits.length+1)+((a.bits.length+1)+(1+(w+((a.bits.length+1)+(v+(u+1))))))),?_,?_⟩
  · change u ≤ 2*a.bits.length+2 at hu
    change v ≤ 2*g.bits.length+2 at hv
    omega
  · simpa [clearWord,← Nat.add_assoc] using h

/-- Both encryption powers, the vote-dependent product and full cleanup execute.
The only input restrictions are the canonical reduced coordinates and p ≥ 2. -/
theorem run (p g pk : Nat) (raw : List Bool) (vote : Bool) (context : List Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    ∃ used ≤ clock p raw.length,
      tick^[used] (start g.bits pk.bits raw p.bits context vote) =
      result ((g^bitsValue raw)%p).bits
        ((((pk^bitsValue raw)%p)*(if vote then g else 1))%p).bits
        g.bits pk.bits raw p.bits context vote := by
  obtain ⟨u,hu,he⟩ := two_powers p g pk raw context vote hp hg hpk
  have hb : (pk^bitsValue raw)%p < p := Nat.mod_lt _ (by omega)
  cases vote
  · have hpeek := peek_vote ((pk^bitsValue raw)%p).bits pk.bits raw p.bits context pk.bits g.bits ((g^bitsValue raw)%p).bits false
    have hclear := clear_state 4 ((pk^bitsValue raw)%p).bits [] [] pk.bits raw p.bits context pk.bits g.bits ((g^bitsValue raw)%p).bits false
    have hhalt := halt_run ((pk^bitsValue raw)%p).bits raw p.bits context pk.bits g.bits ((g^bitsValue raw)%p).bits false
    have h := sequence he (sequence hpeek (sequence hclear hhalt))
    have hpkw : pk.bits.length ≤ p.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hpk.le
    refine ⟨1+((pk.bits.length+1)+(1+u)),?_,?_⟩
    · unfold clock
      omega
    · simpa [clearWord,← Nat.add_assoc] using h
  · obtain ⟨v,hv,hf⟩ := finish_true p ((pk^bitsValue raw)%p) g pk raw context ((g^bitsValue raw)%p).bits hb hg hpk
    exact ⟨v+u,by unfold clock; omega,sequence he hf⟩

/-- Only the final halted state absorbs unused analytical fuel. -/
theorem padded_run (p g pk : Nat) (raw : List Bool) (vote : Bool) (context : List Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    tick^[clock p raw.length] (start g.bits pk.bits raw p.bits context vote) =
      result ((g^bitsValue raw)%p).bits
        ((((pk^bitsValue raw)%p)*(if vote then g else 1))%p).bits
        g.bits pk.bits raw p.bits context vote := by
  obtain ⟨u,hu,he⟩ := run p g pk raw vote context hp hg hpk
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hu
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) d

/-- The local instruction bound is checked against all finite instructions. -/
theorem local_cost (l : Fin 490) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Actual charged execution, derived from the run and instruction audit. -/
theorem charged (p g pk : Nat) (raw : List Bool) (vote : Bool) (context : List Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    ∃ charge ≤ 32*clock p raw.length,
      BitOracleMachine.run code (clock p raw.length) (start g.bits pk.bits raw p.bits context vote) =
      pure (result ((g^bitsValue raw)%p).bits
        ((((pk^bitsValue raw)%p)*(if vote then g else 1))%p).bits
        g.bits pk.bits raw p.bits context vote,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock p raw.length) (start g.bits pk.bits raw p.bits context vote)
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run code (clock p raw.length) (start g.bits pk.bits raw p.bits context vote) =
    pure (tick^[clock p raw.length] (start g.bits pk.bits raw p.bits context vote),charge) at he
  rw [he,padded_run p g pk raw vote context hp hg hpk]

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeEncryptMachine
