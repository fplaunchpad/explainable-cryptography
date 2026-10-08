import ExplainableCrypto.Helios.Computational.PrimeNonceMachineRun
import ExplainableCrypto.Helios.Computational.NonceOperands
import ExplainableCrypto.Helios.Computational.BitOracleStackFrame
import ExplainableCrypto.Helios.Computational.FairBitUniformOracle

/-! Actual nonce sampling and response continuation. Saved words live outside
all eight sampler work ports; the successor consumes the returned index in place. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNonceMachine
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

def sampleLayout : Fin 8 ⊕ Fin 3 ≃ Fin 11 := finSumFinEquiv

def responseLayout : Fin 8 ⊕ Fin 3 ≃ Fin 11 where
  toFun
    | .inl k => ![0,2,3,4,5,8,9,10] k
    | .inr k => ![1,6,7] k
  invFun := ![.inl 0,.inr 0,.inl 1,.inl 2,.inl 3,.inl 4,.inr 1,.inr 2,.inl 5,.inl 6,.inl 7]
  left_inv k := by cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def coinLabel (l : Fin 28) : Fin 55 := ⟨l.val,by omega⟩
def responseLabel (l : Fin 26) : Fin 55 := ⟨l.val+29,by omega⟩

def responseCode : Code 11 26 3 :=
  BitOracleStackFrame.code responseLayout (fun l => .compute (program l))
def coinCode : Code 11 28 3 := BitOracleStackFrame.code sampleLayout CoinScalarMachine.code

def sampleTailCode (l : Fin 55) : Command 11 55 3 :=
  if h : l.val < 28 then BitOracleReturnLink.command coinLabel (some 28) (coinCode ⟨l.val,h⟩)
  else if l = 28 then .compute
    (.branch (fun v => v == 2)
      (.load (fun _ => 0) (.goto (fun _ => responseLabel 0)))
      (.load (fun _ => 1) .halt))
  else BitOracleReturnLink.command responseLabel none (responseCode ⟨l.val-29,by omega⟩)

def sampleTailStart (width : List Bool) (modulus : Nat) (frame : Frame) :
    BitOracleMachine.Config 11 55 3 :=
  BitOracleReturnLink.embed coinLabel (some 28)
    (BitOracleStackFrame.embed sampleLayout (CoinScalarMachine.start width modulus) frame)

def sampleResult (word modulus : List Bool) (frame : Frame) : BitOracleMachine.Config 11 55 3 :=
  ⟨none,2,![[],modulus,[],[],[],word,[],[],frame 0,frame 1,frame 2]⟩

def tailClock (width modulus : Nat) : Nat :=
  CoinScalarMachine.clock width modulus+1+clock (modulus-1)
def tailCost (width modulus : Nat) : Nat :=
  CoinScalarMachine.cost width modulus+3+32*clock (modulus-1)

private theorem coin_code (l : Fin 28) : sampleTailCode (coinLabel l) =
    BitOracleReturnLink.command coinLabel (some 28) (coinCode l) := by
  simp [sampleTailCode,coinLabel,l.isLt]
private theorem response_code (l : Fin 26) : sampleTailCode (responseLabel l) =
    BitOracleReturnLink.command responseLabel none (responseCode l) := by
  fin_cases l <;> rfl

private def responseStart (word modulus : List Bool) (frame : Frame) :
    BitOracleMachine.Config 11 55 3 :=
  BitOracleReturnLink.embed responseLabel none
    (BitOracleStackFrame.embed responseLayout (start word frame) ![modulus,[],[]])

private theorem response_run (fuel : Nat) (cfg : PrimeNonceMachine.Config)
    (modulus : List Bool) :
    run sampleTailCode fuel (BitOracleReturnLink.embed responseLabel none
      (BitOracleStackFrame.embed responseLayout cfg ![modulus,[],[]])) =
      (fun out => (BitOracleReturnLink.embed responseLabel none
        (BitOracleStackFrame.embed responseLayout out.1 ![modulus,[],[]]),out.2)) <$>
      run (fun l => .compute (program l)) fuel cfg := by
  rw [BitOracleReturnLink.rename_run responseCode sampleTailCode responseLabel response_code,
    responseCode,BitOracleStackFrame.run]
  simp only [Functor.map_map]

private theorem uniform_response_charge (modulus n : Nat) (hn : n < modulus)
    (frame : Frame) :
    ∃ charge ≤ 32*clock (modulus-1),
      run (fun l => .compute (program l)) (clock (modulus-1))
        (start (uniformNatEncode n) frame) =
        pure (result (uniformNatEncode (n+1)) frame,charge) := by
  have h₀ := Nat.size_le_size (show n ≤ modulus-1 by omega)
  have h₁ := Nat.size_le_size (show n+1 ≤ modulus-1+1 by omega)
  have hb : clock n ≤ clock (modulus-1) := by
    simp only [clock,SamplerOperands.clock,if_true] at *
    omega
  have he := run_nat n [] frame
  simp only [List.append_nil] at he
  have hh : (TM2ReturnLink.tick program)^[clock (modulus-1)]
      (start (uniformNatEncode n) frame) = result (uniformNatEncode (n+1)) frame := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hb
    rw [hd,Nat.add_comm _ d,Function.iterate_add_apply,he]
    exact Function.iterate_fixed (by rfl) d
  obtain ⟨c,hc,hr⟩ := compute_run_cost program 32 local_cost (clock (modulus-1))
    (start (uniformNatEncode n) frame)
  exact ⟨c,hc,by simpa only [hh] using hr⟩

private theorem response_result (word modulus : List Bool) (frame : Frame) :
    BitOracleReturnLink.embed responseLabel none
      (BitOracleStackFrame.embed responseLayout (result word frame) ![modulus,[],[]]) =
      sampleResult word modulus frame := by
  change (⟨none,2,_⟩ : BitOracleMachine.Config 11 55 3) = ⟨none,2,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

private theorem response_gate (word modulus : List Bool) (frame : Frame) :
    step sampleTailCode (BitOracleReturnLink.embed coinLabel (some 28)
      (BitOracleStackFrame.embed sampleLayout (CoinScalarMachine.result word modulus) frame)) =
      pure (responseStart word modulus frame,3) := by
  apply congrArg pure
  change ((⟨some (responseLabel 0),0,_⟩ : BitOracleMachine.Config 11 55 3),3) =
    ((⟨some (responseLabel 0),0,_⟩ : BitOracleMachine.Config 11 55 3),3)
  congr 2
  funext k; fin_cases k <;> rfl

private theorem after_coin (modulus n : Nat) (hn : n < modulus) (frame : Frame) :
    ∃ charge ≤ 3+32*clock (modulus-1),
      run sampleTailCode (1+clock (modulus-1))
        (BitOracleReturnLink.embed coinLabel (some 28)
          (BitOracleStackFrame.embed sampleLayout
            (CoinScalarMachine.result (uniformNatEncode n) modulus.bits) frame)) =
        pure (sampleResult (uniformNatEncode (n+1)) modulus.bits frame,charge) := by
  obtain ⟨c,hc,he⟩ := uniform_response_charge modulus n hn frame
  refine ⟨3+c,by omega,?_⟩
  rw [Nat.add_comm 1,run,response_gate,pure_bind,responseStart,response_run,he]
  simp only [map_pure,response_result]
  rfl

/-- The complete sampler and response continuation preserve their full coin
query tree and all saved words; both linker halt premises are derived. -/
theorem tail_source (width : List Bool) (modulus : Nat) (hm : 0 < modulus) (frame : Frame) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = width.length → charge bits ≤ tailCost width.length modulus) ∧
      run sampleTailCode (tailClock width.length modulus) (sampleTailStart width modulus frame) =
        (fun bits => (sampleResult (uniformNatEncode (bitsValue bits % modulus+1)) modulus.bits frame,
          charge bits)) <$> CoinWordLoader.word width.length := by
  obtain ⟨coinCharge,hcoin,hcoinRun⟩ := CoinScalarMachine.run_source width modulus hm
  have hfr : run coinCode (CoinScalarMachine.clock width.length modulus)
      (BitOracleStackFrame.embed sampleLayout (CoinScalarMachine.start width modulus) frame) =
      (fun bits => (BitOracleStackFrame.embed sampleLayout
        (CoinScalarMachine.result (uniformNatEncode (bitsValue bits % modulus)) modulus.bits) frame,
        coinCharge bits)) <$> CoinWordLoader.word width.length := by
    rw [coinCode,BitOracleStackFrame.run,hcoinRun]
    simp only [Functor.map_map]
  choose responseCharge hresponse hresponseRun using fun bits =>
    after_coin modulus (bitsValue bits % modulus) (Nat.mod_lt _ hm) frame
  have hh : ∀ out ∈ support (run coinCode (CoinScalarMachine.clock width.length modulus)
      (BitOracleStackFrame.embed sampleLayout (CoinScalarMachine.start width modulus) frame)),
      out.1.l = none := by
    intro out ho
    rw [hfr] at ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rfl
  have hc : ∀ out ∈ support (run coinCode (CoinScalarMachine.clock width.length modulus)
      (BitOracleStackFrame.embed sampleLayout (CoinScalarMachine.start width modulus) frame)),
      ∀ last ∈ support (run sampleTailCode (1+clock (modulus-1))
        (BitOracleReturnLink.embed coinLabel (some 28) out.1)), last.1.l = none := by
    intro out ho
    rw [hfr] at ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    intro last hl
    rw [hresponseRun] at hl
    have he := eq_of_mem_support_pure _ hl
    subst last
    rfl
  have hr := BitOracleReturnLink.run coinCode sampleTailCode coinLabel 28 coin_code
    (CoinScalarMachine.clock width.length modulus) (1+clock (modulus-1))
    (BitOracleStackFrame.embed sampleLayout (CoinScalarMachine.start width modulus) frame) hh hc
  refine ⟨fun bits => coinCharge bits+responseCharge bits,?_,?_⟩
  · intro bits hb
    have h₁ := hcoin bits hb
    have h₂ := hresponse bits
    change coinCharge bits+responseCharge bits ≤ _
    unfold tailCost
    omega
  · rw [tailClock,Nat.add_assoc,sampleTailStart,hr,hfr]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    apply bind_congr
    intro bits
    rw [hresponseRun]
    rfl


def operandLabel (l : Fin NonceOperands.size) : Fin 71 := ⟨l.val,by have := l.isLt; simp only [NonceOperands.size] at *; omega⟩
def tailLabel (l : Fin 55) : Fin 71 := ⟨l.val+16,by omega⟩

def operandCode : Code 11 NonceOperands.size 3 := BitOracleStackFrame.code sampleLayout NonceOperands.code

def sampleCode (l : Fin 71) : Command 11 71 3 :=
  if h : l.val < 15 then BitOracleReturnLink.command operandLabel (some 15) (operandCode ⟨l.val,h⟩)
  else if l = 15 then .compute
    (.branch (fun v => v == 0)
      (.peek 4 (fun _ b => CoinWordLoader.encode b)
        (.branch (fun v => v == 0)
          (.load (fun _ => 0) (.goto (fun _ => tailLabel (coinLabel 15))))
          (.load (fun _ => 1) .halt)))
      (.load (fun _ => 1) .halt))
  else BitOracleReturnLink.command tailLabel none (sampleTailCode ⟨l.val-16,by omega⟩)

def sampleStart (word : List Bool) (frame : Frame) : BitOracleMachine.Config 11 71 3 :=
  BitOracleReturnLink.embed operandLabel (some 15)
    (BitOracleStackFrame.embed sampleLayout (NonceOperands.startWord word) frame)
def sampleOutput (word modulus : List Bool) (frame : Frame) : BitOracleMachine.Config 11 71 3 :=
  BitOracleReturnLink.embed tailLabel none (sampleResult word modulus frame)
def sampleWidth (slack q : Nat) : Nat := (q-1).size+slack
def sampleClock (slack q : Nat) : Nat :=
  NonceOperands.clock slack q+1+tailClock (sampleWidth slack q) (q-1)
def sampleCost (slack q : Nat) : Nat :=
  NonceOperands.cost slack q+5+tailCost (sampleWidth slack q) (q-1)

#print axioms tail_source
end ExplainableCrypto.Helios.Computational.PrimeNonceMachine
