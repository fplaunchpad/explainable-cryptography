import ExplainableCrypto.Helios.Computational.PrimeEncryptMachineSource
import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachineRun
/-! Actual joint nonce sampling, digit routing and first ciphertext execution. -/

namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
open Turing.TM2 OracleComp OracleSpec BitOracleMachine

abbrev Route := PrimeNonceCiphertextMachine.Config

def size : Nat := 655
instance : NeZero size := ⟨by decide⟩
def routeLabel (l : Fin 7) : Fin size := ⟨1+l.val,by unfold size; omega⟩
def pairLabel (l : Fin PrimeNoncePairMachine.size) : Fin size :=
  ⟨8+l.val,by have := l.isLt; simp only [PrimeNoncePairMachine.size,PrimeNoncePairTransport.size] at this; unfold size; omega⟩
def encryptLabel (l : Fin 490) : Fin size := ⟨165+l.val,by unfold size; omega⟩

def pairCode : Code 23 PrimeNoncePairMachine.size 3 :=
  BitOracleStackFrame.code PrimeNonceCiphertextMachine.pairLayout PrimeNoncePairMachine.code

def encryptCode : Code 23 490 3 :=
  BitOracleStackFrame.code PrimeNonceCiphertextMachine.encryptLayout PrimeEncryptMachine.code

def code (l : Fin size) : Command 23 size 3 :=
  if l = 0 then .compute
    (.branch (fun v => v == 2)
      (.load (fun _ => 0) (.goto (fun _ => encryptLabel (PrimeEncryptMachine.copyLabel 0 0))))
      (.load (fun _ => 1) .halt))
  else if h : l.val < 8 then
    BitOracleReturnLink.command routeLabel (some 0)
      (PrimeNonceCiphertextMachine.code ⟨l.val-1,by omega⟩)
  else if h : l.val < 165 then
    BitOracleReturnLink.command pairLabel (some (routeLabel 0))
      (pairCode ⟨l.val-8,by simp only [PrimeNoncePairMachine.size,PrimeNoncePairTransport.size]; omega⟩)
  else BitOracleReturnLink.command encryptLabel none
    (encryptCode ⟨l.val-165,by have := l.isLt; unfold size at this; omega⟩)

abbrev Config := BitOracleMachine.Config 23 size 3

def start (g pk modulus record context : List Bool) (vote : Bool) : Config :=
  BitOracleReturnLink.embed pairLabel (some (routeLabel 0))
    (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.pairLayout
      (PrimeNoncePairMachine.start record context)
      (PrimeNonceCiphertextMachine.pairFrame modulus g pk vote))

def result (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) : Config :=
  ⟨none,2,![beta,[],[],[],[],[],modulus,[],[],[],[],[],[],nonce,context,pk,g,alpha,[vote],record,first,second,samplerMod]⟩

def clock (slack p q : Nat) : Nat := PrimeNoncePairMachine.clock slack q +
  (PrimeNonceCiphertextMachine.clock (q-1) + 1 + PrimeEncryptMachine.clock p (q-1).size)

def cost (slack p q : Nat) : Nat := PrimeNoncePairMachine.cost slack q +
  (6*PrimeNonceCiphertextMachine.clock (q-1) + 3 + 32*PrimeEncryptMachine.clock p (q-1).size)

end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller

namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
open Turing.TM2 OracleComp OracleSpec BitOracleMachine

private theorem route_code (l : Fin 7) : code (routeLabel l) =
    BitOracleReturnLink.command routeLabel (some 0) (PrimeNonceCiphertextMachine.code l) := by
  fin_cases l <;> rfl
private theorem pair_code (l : Fin PrimeNoncePairMachine.size) : code (pairLabel l) =
    BitOracleReturnLink.command pairLabel (some (routeLabel 0)) (pairCode l) := by
  fin_cases l <;> rfl
set_option maxRecDepth 4096 in
private theorem encrypt_code (l : Fin 490) : code (encryptLabel l) =
    BitOracleReturnLink.command encryptLabel none (encryptCode l) := by
  fin_cases l <;> rfl

def encryptFrame (record first second samplerMod : List Bool) : Fin 4 → List Bool :=
  ![record,first,second,samplerMod]

private theorem pair_route (record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) :
    BitOracleReturnLink.embed pairLabel (some (routeLabel 0))
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.pairLayout
        (PrimeNoncePairMachine.result record first second samplerMod context)
        (PrimeNonceCiphertextMachine.pairFrame modulus g pk vote)) =
    BitOracleReturnLink.embed routeLabel (some 0)
      (PrimeNonceCiphertextMachine.start record first second samplerMod context modulus g pk vote) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

private theorem route_gate (nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) :
    step code (BitOracleReturnLink.embed routeLabel (some 0)
      (PrimeNonceCiphertextMachine.result nonce record first second samplerMod context modulus g pk vote)) =
      pure (BitOracleReturnLink.embed encryptLabel none
        (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
          (PrimeEncryptMachine.start g pk nonce modulus context vote)
          (encryptFrame record first second samplerMod)),3) := by
  change (pure ((⟨_,_,_⟩ : Config),3) : OracleComp spec (Config × Nat)) = pure (_,3)
  apply congrArg (fun cfg : Config => (pure (cfg,3) : OracleComp spec (Config × Nat)))
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

private theorem encrypt_result (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) :
    BitOracleReturnLink.embed encryptLabel none
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
        (PrimeEncryptMachine.result alpha beta g pk nonce modulus context vote)
        (encryptFrame record first second samplerMod)) =
    result alpha beta nonce record first second samplerMod context modulus g pk vote := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller

namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem encrypt_clock_mono (p n bound : Nat) (hn : n ≤ bound) :
    PrimeEncryptMachine.clock p n ≤ PrimeEncryptMachine.clock p bound := by
  unfold PrimeEncryptMachine.clock BinaryModPower.clock
  nlinarith

private theorem encrypt_bounded (p g pk n bound : Nat) (hn : n ≤ bound)
    (record first second samplerMod context : List Bool) (vote : Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    ∃ charge ≤ 32*PrimeEncryptMachine.clock p bound.size,
      BitOracleMachine.run code (PrimeEncryptMachine.clock p bound.size)
        (BitOracleReturnLink.embed encryptLabel none
          (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
            (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context vote)
            (encryptFrame record first second samplerMod))) =
      pure (result (g^n%p).bits (((pk^n%p)*(if vote then g else 1))%p).bits
        n.bits record first second samplerMod context p.bits g.bits pk.bits vote,charge) := by
  obtain ⟨c,hc,he⟩ := PrimeEncryptMachine.charged p g pk n.bits vote context hp hg hpk
  have ht := encrypt_clock_mono p n.size bound.size (Nat.size_le_size hn)
  simp only [Nat.size_eq_bits_len,bitsValue_bits] at hc he
  have hpadded := BitOracleReturnLink.padded PrimeEncryptMachine.code
    (PrimeEncryptMachine.clock p n.size)
    (PrimeEncryptMachine.clock p bound.size-PrimeEncryptMachine.clock p n.size)
    (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context vote)
    (by rw [he]; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out; rfl)
  rw [Nat.sub_add_cancel ht,he] at hpadded
  have hf := BitOracleStackFrame.run PrimeNonceCiphertextMachine.encryptLayout
    PrimeEncryptMachine.code (PrimeEncryptMachine.clock p bound.size)
    (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context vote)
    (encryptFrame record first second samplerMod)
  rw [hpadded] at hf
  have hr := BitOracleReturnLink.rename_run encryptCode code encryptLabel encrypt_code
    (PrimeEncryptMachine.clock p bound.size)
    (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
      (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context vote)
      (encryptFrame record first second samplerMod))
  unfold encryptCode at hr
  rw [hf] at hr
  refine ⟨c,hc.trans (Nat.mul_le_mul_left 32 ht),?_⟩
  simpa only [map_pure,encrypt_result] using hr

private theorem gate_encrypt (p g pk n bound : Nat) (hn : n ≤ bound)
    (record first second samplerMod context : List Bool) (vote : Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    ∃ charge ≤ 3+32*PrimeEncryptMachine.clock p bound.size,
      BitOracleMachine.run code (1+PrimeEncryptMachine.clock p bound.size)
        (BitOracleReturnLink.embed routeLabel (some 0)
          (PrimeNonceCiphertextMachine.result n.bits record first second samplerMod context p.bits g.bits pk.bits vote)) =
      pure (result (g^n%p).bits (((pk^n%p)*(if vote then g else 1))%p).bits
        n.bits record first second samplerMod context p.bits g.bits pk.bits vote,charge) := by
  obtain ⟨c,hc,he⟩ := encrypt_bounded p g pk n bound hn record first second samplerMod context vote hp hg hpk
  refine ⟨3+c,by omega,?_⟩
  rw [Nat.add_comm 1,BitOracleMachine.run,route_gate]
  simp only [pure_bind,he]

/-- Actual prefix extraction, successful reset, and ciphertext execution at the
fixed public scalar-width bound. Every retained word and all cleanup are exact. -/
theorem continuation (p g pk n bound : Nat) (hn : n ≤ bound)
    (record second samplerMod context : List Bool) (vote : Bool)
    (hp : 2 ≤ p) (hg : g < p) (hpk : pk < p) :
    ∃ charge ≤ 6*PrimeNonceCiphertextMachine.clock bound+3+32*PrimeEncryptMachine.clock p bound.size,
      BitOracleMachine.run code
        (PrimeNonceCiphertextMachine.clock bound+(1+PrimeEncryptMachine.clock p bound.size))
        (BitOracleReturnLink.embed routeLabel (some 0)
          (PrimeNonceCiphertextMachine.start record (uniformNatEncode n) second samplerMod context p.bits g.bits pk.bits vote)) =
      pure (result (g^n%p).bits (((pk^n%p)*(if vote then g else 1))%p).bits
        n.bits record (uniformNatEncode n) second samplerMod context p.bits g.bits pk.bits vote,charge) := by
  obtain ⟨c,hc,he⟩ := PrimeNonceCiphertextMachine.charged_bounded n bound hn
    record second samplerMod context p.bits g.bits pk.bits vote
  obtain ⟨d,hd,hf⟩ := gate_encrypt p g pk n bound hn record (uniformNatEncode n) second samplerMod context vote hp hg hpk
  have hh : ∀ out ∈ support (BitOracleMachine.run PrimeNonceCiphertextMachine.code
      (PrimeNonceCiphertextMachine.clock bound)
      (PrimeNonceCiphertextMachine.start record (uniformNatEncode n) second samplerMod context p.bits g.bits pk.bits vote)),
      out.1.l = none := by
    rw [he]; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out; rfl
  have hhalt : ∀ out ∈ support (BitOracleMachine.run PrimeNonceCiphertextMachine.code
      (PrimeNonceCiphertextMachine.clock bound)
      (PrimeNonceCiphertextMachine.start record (uniformNatEncode n) second samplerMod context p.bits g.bits pk.bits vote)),
      ∀ last ∈ support (BitOracleMachine.run code (1+PrimeEncryptMachine.clock p bound.size)
        (BitOracleReturnLink.embed routeLabel (some 0) out.1)), last.1.l = none := by
    rw [he]; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out
    rw [hf]; intro last hl; have hv := eq_of_mem_support_pure _ hl; subst last; rfl
  refine ⟨c+d,by omega,?_⟩
  rw [BitOracleReturnLink.run _ _ _ _ route_code _ _ _ hh hhalt,he,pure_bind,hf,pure_bind]

end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller

namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- Numeric value of the executed nonzero scalar sampler on its actual word. -/
def nonce (q : Nat) (bits : List Bool) : Nat := bitsValue bits%(q-1)+1

/-- Full actual output in the independent integer presentation. The source
instance identifies these coordinates with the historical encryptWith result. -/
def numericResult (slack p q g pk : Nat) (context : List Bool) (vote : Bool)
    (a b : List Bool) : Config :=
  result (g^nonce q a%p).bits (((pk^nonce q a%p)*(if vote then g else 1))%p).bits
    (nonce q a).bits (SamplerOperands.input slack q [])
    (uniformNatEncode (nonce q a)) (uniformNatEncode (nonce q b)) (q-1).bits
    context p.bits g.bits pk.bits vote

private theorem nonce_le (q : Nat) (hq : 2 ≤ q) (a : List Bool) : nonce q a ≤ q-1 := by
  have h := Nat.mod_lt (bitsValue a) (show 0 < q-1 by omega)
  unfold nonce
  omega

end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller

namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- One uninterrupted actual controller preserves the two successive nonce
draws, complete retained state, and a charge derived from all three executions. -/
theorem caller_run (slack p q g pk : Nat) (hq : 2 ≤ q) (hp : 2 ≤ p)
    (hg : g < p) (hpk : pk < p) (context : List Bool) (vote : Bool) :
    ∃ charge : List Bool → List Bool → Nat,
      (∀ a, a.length = PrimeNonceMachine.sampleWidth slack q →
        ∀ b, b.length = PrimeNonceMachine.sampleWidth slack q → charge a b ≤ cost slack p q) ∧
      BitOracleMachine.run code (clock slack p q)
        (start g.bits pk.bits p.bits (SamplerOperands.input slack q []) context vote) = (do
        let a ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        let b ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        pure (numericResult slack p q g pk context vote a b,charge a b)) := by
  classical
  obtain ⟨c,hc,he⟩ := PrimeNoncePairMachine.pair_run slack q hq context
  have framed : BitOracleMachine.run pairCode (PrimeNoncePairMachine.clock slack q)
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.pairLayout
        (PrimeNoncePairMachine.start (SamplerOperands.input slack q []) context)
        (PrimeNonceCiphertextMachine.pairFrame p.bits g.bits pk.bits vote)) = (do
      let a ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
      let b ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
      pure (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.pairLayout
        (PrimeNoncePairMachine.result (SamplerOperands.input slack q [])
          (uniformNatEncode (nonce q a)) (uniformNatEncode (nonce q b)) (q-1).bits context)
        (PrimeNonceCiphertextMachine.pairFrame p.bits g.bits pk.bits vote),c a b)) := by
    have hf := BitOracleStackFrame.run PrimeNonceCiphertextMachine.pairLayout
      PrimeNoncePairMachine.code (PrimeNoncePairMachine.clock slack q)
      (PrimeNoncePairMachine.start (SamplerOperands.input slack q []) context)
      (PrimeNonceCiphertextMachine.pairFrame p.bits g.bits pk.bits vote)
    rw [he] at hf
    simpa only [pairCode,nonce,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def] using hf
  have tail (a b : List Bool) :
      ∃ d ≤ 6*PrimeNonceCiphertextMachine.clock (q-1)+3+32*PrimeEncryptMachine.clock p (q-1).size,
        BitOracleMachine.run code
          (PrimeNonceCiphertextMachine.clock (q-1)+(1+PrimeEncryptMachine.clock p (q-1).size))
          (BitOracleReturnLink.embed pairLabel (some (routeLabel 0))
            (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.pairLayout
              (PrimeNoncePairMachine.result (SamplerOperands.input slack q [])
                (uniformNatEncode (nonce q a)) (uniformNatEncode (nonce q b)) (q-1).bits context)
              (PrimeNonceCiphertextMachine.pairFrame p.bits g.bits pk.bits vote))) =
          pure (numericResult slack p q g pk context vote a b,d) := by
    rw [pair_route]
    exact continuation p g pk (nonce q a) (q-1) (nonce_le q hq a)
      (SamplerOperands.input slack q []) (uniformNatEncode (nonce q b)) (q-1).bits context vote hp hg hpk
  choose d hd ht using tail
  have hh : ∀ out ∈ support (BitOracleMachine.run pairCode (PrimeNoncePairMachine.clock slack q)
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.pairLayout
        (PrimeNoncePairMachine.start (SamplerOperands.input slack q []) context)
        (PrimeNonceCiphertextMachine.pairFrame p.bits g.bits pk.bits vote))), out.1.l = none := by
    rw [framed]
    intro out ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨a,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨b,_,ho⟩ := ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rfl
  have hhalt : ∀ out ∈ support (BitOracleMachine.run pairCode (PrimeNoncePairMachine.clock slack q)
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.pairLayout
        (PrimeNoncePairMachine.start (SamplerOperands.input slack q []) context)
        (PrimeNonceCiphertextMachine.pairFrame p.bits g.bits pk.bits vote))),
      ∀ last ∈ support (BitOracleMachine.run code
        (PrimeNonceCiphertextMachine.clock (q-1)+(1+PrimeEncryptMachine.clock p (q-1).size))
        (BitOracleReturnLink.embed pairLabel (some (routeLabel 0)) out.1)), last.1.l = none := by
    rw [framed]
    intro out ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨a,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨b,_,ho⟩ := ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rw [ht]
    intro last hl
    have hv := eq_of_mem_support_pure _ hl
    subst last
    rfl
  refine ⟨fun a b => c a b+d a b,?_,?_⟩
  · intro a ha b hb
    have hc' := hc a ha b hb
    have hd' := hd a b
    change c a b+d a b ≤ _
    unfold cost
    omega
  · simp only [clock,Nat.add_assoc,start]
    rw [BitOracleReturnLink.run _ _ _ _ pair_code _ _ _ hh hhalt,framed]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro a
    apply bind_congr
    intro b
    rw [ht]
    rfl

#print axioms continuation
#print axioms caller_run
end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
