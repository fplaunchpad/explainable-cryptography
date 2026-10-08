import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextMachineRun
import ExplainableCrypto.Helios.Computational.PrimeEncryptMachineRun
import ExplainableCrypto.Helios.Computational.PrimeTranscriptDrawsRun

namespace ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem route_code (l : Fin 7) : code (routeLabel l) =
    BitOracleReturnLink.command routeLabel (some 1) (routeCode l) := by
  fin_cases l <;> rfl

set_option maxRecDepth 4096 in
theorem encrypt_code (l : Fin 490) : code (encryptLabel l) =
    BitOracleReturnLink.command encryptLabel
      (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0))) (encryptCode l) := by
  have h0 : encryptLabel l ≠ 0 := by intro he; have := congrArg Fin.val he; change 9+l.val = 0 at this; omega
  have h1 : encryptLabel l ≠ 1 := by intro he; have := congrArg Fin.val he; change 9+l.val = 1 at this; omega
  have h2 : ¬ (encryptLabel l).val < 9 := by dsimp [encryptLabel]; omega
  have h3 : (encryptLabel l).val < 499 := by dsimp [encryptLabel]; omega
  simp only [code,if_neg h0,if_neg h1,dif_neg h2,dif_pos h3]
  simp only [encryptLabel,Nat.add_sub_cancel_left]

theorem draw_code (l : Fin PrimeTranscriptDraws.size) : code (drawLabel l) =
    BitOracleReturnLink.command drawLabel none (drawsCode l) := by
  have h0 : drawLabel l ≠ 0 := by intro he; have := congrArg Fin.val he; change 499+l.val = 0 at this; omega
  have h1 : drawLabel l ≠ 1 := by intro he; have := congrArg Fin.val he; change 499+l.val = 1 at this; omega
  have h2 : ¬ (drawLabel l).val < 9 := by dsimp [drawLabel]; omega
  have h3 : ¬ (drawLabel l).val < 499 := by dsimp [drawLabel]; omega
  simp only [code,if_neg h0,if_neg h1,dif_neg h2,dif_neg h3]
  simp only [drawLabel,Nat.add_sub_cancel_left]

def encryptFrame (record first second samplerMod : List Bool) : Fin 4 → List Bool :=
  ![record,first,second,samplerMod]

private theorem entry_step (words : Fin 59 → List Bool) :
    BitOracleMachine.step code (⟨some 0,2,words⟩ : Config) =
      pure ((⟨some (routeLabel 0),2,Function.update words 53 (false :: words 53)⟩ : Config),3) := rfl

private theorem reset_step (words : Fin 59 → List Bool) :
    BitOracleMachine.step code (⟨some 1,2,words⟩ : Config) =
      pure ((⟨some (encryptLabel (PrimeEncryptMachine.copyLabel 0 0)),0,words⟩ : Config),3) := rfl

attribute [local irreducible] code

private theorem input_entry_state (record first second samplerMod context modulus g pk : List Bool)
    (frame : Fin 36 → List Bool) :
    (⟨some (routeLabel 0),2,Function.update
      (start (inputWords record first second samplerMod context modulus g pk frame)).stk
      53 [false]⟩ : Config) =
    BitOracleReturnLink.embed routeLabel (some 1)
      (BitOracleStackFrame.embed layout
        (PrimeNonceCiphertextMachine.start record first second samplerMod context modulus g pk false) frame) := by
  have hw (k : Fin 59) :
      (Function.update
        (start (inputWords record first second samplerMod context modulus g pk frame)).stk
        53 [false]) k =
      (BitOracleStackFrame.embed layout
        (PrimeNonceCiphertextMachine.start record first second samplerMod context modulus g pk false) frame).stk k := by
    obtain ⟨x,rfl⟩ := layout.surjective k
    cases x with
    | inl i =>
      simp only [start,inputWords,BitOracleStackFrame.embed,TM2StackFrame.embed,
        TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl,Fin.eta]
      fin_cases i <;> rfl
    | inr j =>
      simp only [start,inputWords,BitOracleStackFrame.embed,TM2StackFrame.embed,
        TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr,Fin.eta]
      fin_cases j <;> rfl
  exact congrArg (fun words : Fin 59 → List Bool =>
    (⟨some (routeLabel 0),2,words⟩ : Config)) (funext hw)

theorem input_entry (record first second samplerMod context modulus g pk : List Bool)
    (frame : Fin 36 → List Bool) :
    step code (start (inputWords record first second samplerMod context modulus g pk frame)) =
      pure (BitOracleReturnLink.embed routeLabel (some 1)
        (BitOracleStackFrame.embed layout
          (PrimeNonceCiphertextMachine.start record first second samplerMod context modulus g pk false) frame),3) := by
  change BitOracleMachine.step code
    (⟨some 0,2,(start (inputWords record first second samplerMod context modulus g pk frame)).stk⟩ : Config) = _
  rw [entry_step]
  change (pure ((⟨some (routeLabel 0),2,Function.update
    (start (inputWords record first second samplerMod context modulus g pk frame)).stk 53 [false]⟩ : Config),3)
    : OracleComp spec (Config × Nat)) = _
  rw [input_entry_state]

theorem route_return (nonce record first second samplerMod context modulus g pk : List Bool)
    (frame : Fin 36 → List Bool) :
    step code (BitOracleReturnLink.embed routeLabel (some 1)
      (BitOracleStackFrame.embed layout
        (PrimeNonceCiphertextMachine.result nonce record first second samplerMod context modulus g pk false) frame)) =
    pure (BitOracleReturnLink.embed encryptLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (BitOracleStackFrame.embed layout
        (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
          (PrimeEncryptMachine.start g pk nonce modulus context false)
          (encryptFrame record first second samplerMod)) frame),3) := by
  have hl (k : Fin 23) :
      (PrimeNonceCiphertextMachine.result nonce record first second samplerMod context modulus g pk false).stk k =
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
        (PrimeEncryptMachine.start g pk nonce modulus context false)
        (encryptFrame record first second samplerMod)).stk k := by
    fin_cases k <;> rfl
  have hw := congrArg (fun words : Fin 23 → List Bool => TM2StackFrame.data layout words frame) (funext hl)
  have hc : (⟨some (encryptLabel (PrimeEncryptMachine.copyLabel 0 0)),0,
      (BitOracleStackFrame.embed layout
        (PrimeNonceCiphertextMachine.result nonce record first second samplerMod context modulus g pk false) frame).stk⟩ : Config) =
      BitOracleReturnLink.embed encryptLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
        (BitOracleStackFrame.embed layout
          (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
            (PrimeEncryptMachine.start g pk nonce modulus context false)
            (encryptFrame record first second samplerMod)) frame) :=
    congrArg (fun words : Fin 59 → List Bool =>
      (⟨some (encryptLabel (PrimeEncryptMachine.copyLabel 0 0)),0,words⟩ : Config)) hw
  change BitOracleMachine.step code (⟨some 1,2,
    (BitOracleStackFrame.embed layout
      (PrimeNonceCiphertextMachine.result nonce record first second samplerMod context modulus g pk false) frame).stk⟩ : Config) = _
  rw [reset_step,hc]

theorem encrypt_return (alpha beta nonce record first second samplerMod context modulus g pk : List Bool)
    (frame : Fin 36 → List Bool) :
    BitOracleReturnLink.embed encryptLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (BitOracleStackFrame.embed layout
        (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
          (PrimeEncryptMachine.result alpha beta g pk nonce modulus context false)
          (encryptFrame record first second samplerMod)) frame) =
    BitOracleReturnLink.embed drawLabel none
      (BitOracleStackFrame.embed layout
        (PrimeTranscriptDraws.start alpha beta nonce record first second samplerMod context modulus g pk false) frame) := by
  have hs (k : Fin 23) :
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
        (PrimeEncryptMachine.result alpha beta g pk nonce modulus context false)
        (encryptFrame record first second samplerMod)).stk k =
      (PrimeTranscriptDraws.start alpha beta nonce record first second samplerMod context modulus g pk false).stk k := by
    obtain ⟨x,rfl⟩ := PrimeNonceCiphertextMachine.encryptLayout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inl]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleStackFrame.embed,TM2StackFrame.embed,TM2StackFrame.data,
        Equiv.symm_apply_apply,Sum.elim_inr]
      fin_cases j <;> rfl
  have hd := congrArg (fun words : Fin 23 → List Bool => TM2StackFrame.data layout words frame) (funext hs)
  exact congrArg (fun words => (⟨some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)),2,words⟩ : Config)) hd


theorem draws_result (alpha beta nonce c e z0 z1 scalarMod record first second samplerMod context modulus g pk : List Bool)
    (frame : Fin 36 → List Bool) :
    BitOracleReturnLink.embed drawLabel none
      (BitOracleStackFrame.embed layout
        (PrimeTranscriptDraws.result c e z0 z1 scalarMod alpha beta nonce record first second samplerMod context modulus g pk false) frame) =
    result alpha beta nonce c e z0 z1 scalarMod
      (inputWords record first second samplerMod context modulus g pk frame) := by
  have hs (k : Fin 59) :
      (BitOracleReturnLink.embed drawLabel none
      (BitOracleStackFrame.embed layout
        (PrimeTranscriptDraws.result c e z0 z1 scalarMod alpha beta nonce record first second samplerMod context modulus g pk false) frame)).stk k =
      (result alpha beta nonce c e z0 z1 scalarMod
      (inputWords record first second samplerMod context modulus g pk frame)).stk k := by
    obtain ⟨x,rfl⟩ := layout.surjective k
    cases x with
    | inl i =>
      simp only [BitOracleReturnLink.embed,BitOracleStackFrame.embed,TM2StackFrame.embed,
        result,inputWords,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl,Fin.eta]
      fin_cases i <;> rfl
    | inr j =>
      simp only [BitOracleReturnLink.embed,BitOracleStackFrame.embed,TM2StackFrame.embed,
        result,inputWords,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inr,Fin.eta]
      fin_cases j <;> rfl
  exact congrArg (fun words => (⟨none,2,words⟩ : Config)) (funext hs)

#print axioms route_code
#print axioms encrypt_code
#print axioms draw_code
#print axioms input_entry
#print axioms route_return
#print axioms encrypt_return
#print axioms draws_result
end ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
namespace ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
attribute [local irreducible] BitOracleMachine.run code

private theorem encrypt_clock_mono (p a b : Nat) (h : a ≤ b) :
    PrimeEncryptMachine.clock p a ≤ PrimeEncryptMachine.clock p b := by
  unfold PrimeEncryptMachine.clock BinaryModPower.clock
  nlinarith

/-- The actual second-nonce route, false-vote encryption and four fresh draws,
with every earlier word retained and the actual summed execution charge. -/
theorem charged (slack p q g pk n : Nat) (hp : 2 ≤ p) (hg : g < p)
    (hpk : pk < p) (hn : n < q) (second samplerMod context : List Bool)
    (frame : Fin 36 → List Bool) :
    ∃ charge : List Bool → List Bool → List Bool → List Bool → Nat,
      (∀ c, c.length = q.size+slack → ∀ e, e.length = q.size+slack →
        ∀ z0, z0.length = q.size+slack → ∀ z1, z1.length = q.size+slack →
          charge c e z0 z1 ≤ cost slack p q) ∧
      BitOracleMachine.run code (clock slack p q)
        (start (inputWords (SamplerOperands.input slack q []) (uniformNatEncode n)
          second samplerMod context p.bits g.bits pk.bits frame)) = (do
        let c ← CoinWordLoader.word (q.size+slack)
        let e ← CoinWordLoader.word (q.size+slack)
        let z0 ← CoinWordLoader.word (q.size+slack)
        let z1 ← CoinWordLoader.word (q.size+slack)
        pure (result (g^n%p).bits (pk^n%p).bits n.bits
          (uniformNatEncode (bitsValue c % q)) (uniformNatEncode (bitsValue e % q))
          (uniformNatEncode (bitsValue z0 % q)) (uniformNatEncode (bitsValue z1 % q)) q.bits
          (inputWords (SamplerOperands.input slack q []) (uniformNatEncode n)
            second samplerMod context p.bits g.bits pk.bits frame),charge c e z0 z1)) := by
  classical
  have hq : 0 < q := by omega
  have hnb : n ≤ q-1 := by omega
  let record := SamplerOperands.input slack q []
  let first := uniformNatEncode n
  let E := PrimeEncryptMachine.clock p (q-1).size
  let R := PrimeNonceCiphertextMachine.clock (q-1)
  let D := PrimeTranscriptDraws.clock slack q
  let ds := PrimeTranscriptDraws.start (g^n%p).bits (pk^n%p).bits n.bits
    record first second samplerMod context p.bits g.bits pk.bits false
  let es := BitOracleStackFrame.embed layout
    (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
      (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context false)
      (encryptFrame record first second samplerMod)) frame
  let er := BitOracleStackFrame.embed layout
    (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
      (PrimeEncryptMachine.result (g^n%p).bits (pk^n%p).bits g.bits pk.bits n.bits p.bits context false)
      (encryptFrame record first second samplerMod)) frame
  let rs := BitOracleStackFrame.embed layout
    (PrimeNonceCiphertextMachine.start record first second samplerMod context p.bits g.bits pk.bits false) frame
  let rr := BitOracleStackFrame.embed layout
    (PrimeNonceCiphertextMachine.result n.bits record first second samplerMod context p.bits g.bits pk.bits false) frame
  obtain ⟨cd,hcd,hd⟩ := PrimeTranscriptDraws.charged slack q hq
    (g^n%p).bits (pk^n%p).bits n.bits first second samplerMod context p.bits g.bits pk.bits false
  let output := fun c e z0 z1 : List Bool => result (g^n%p).bits (pk^n%p).bits n.bits
    (uniformNatEncode (bitsValue c % q)) (uniformNatEncode (bitsValue e % q))
    (uniformNatEncode (bitsValue z0 % q)) (uniformNatEncode (bitsValue z1 % q)) q.bits
    (inputWords record first second samplerMod context p.bits g.bits pk.bits frame)
  let tree : OracleComp spec (Config × Nat) := do
    let c ← CoinWordLoader.word (q.size+slack)
    let e ← CoinWordLoader.word (q.size+slack)
    let z0 ← CoinWordLoader.word (q.size+slack)
    let z1 ← CoinWordLoader.word (q.size+slack)
    pure (output c e z0 z1,cd c e z0 z1)
  have hdRun : BitOracleMachine.run code D
      (BitOracleReturnLink.embed drawLabel none (BitOracleStackFrame.embed layout ds frame)) = tree := by
    have hf := BitOracleStackFrame.run layout PrimeTranscriptDraws.code D ds frame
    change BitOracleMachine.run PrimeTranscriptDraws.code D ds = _ at hd
    rw [hd] at hf
    rw [BitOracleReturnLink.rename_run _ _ _ draw_code]
    unfold drawsCode
    rw [hf]
    simp only [map_bind,map_pure,draws_result]
    rfl
  have htree : ∀ out ∈ support tree, out.1.l = none := by
    intro out ho
    dsimp [tree] at ho
    rw [mem_support_bind_iff] at ho; obtain ⟨c,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho; obtain ⟨e,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho; obtain ⟨z0,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho; obtain ⟨z1,_,ho⟩ := ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rfl
  obtain ⟨ce,hce,he⟩ := PrimeEncryptMachine.charged p g pk n.bits false context hp hg hpk
  simp only [Nat.size_eq_bits_len,bitsValue_bits] at hce he
  have he' : BitOracleMachine.run PrimeEncryptMachine.code (PrimeEncryptMachine.clock p n.size)
      (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context false) =
      pure (PrimeEncryptMachine.result (g^n%p).bits (pk^n%p).bits g.bits pk.bits n.bits p.bits context false,ce) := by
    simpa only [Bool.false_eq_true,if_false,Nat.mul_one,Nat.mod_mod] using he
  have hE := encrypt_clock_mono p n.size (q-1).size (Nat.size_le_size hnb)
  have hePad := BitOracleReturnLink.padded PrimeEncryptMachine.code
    (PrimeEncryptMachine.clock p n.size) (E-PrimeEncryptMachine.clock p n.size)
    (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context false)
    (by rw [he']; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out; rfl)
  change PrimeEncryptMachine.clock p n.size ≤ E at hE
  rw [Nat.sub_add_cancel hE,he'] at hePad
  have heRun : BitOracleMachine.run encryptCode E es = pure (er,ce) := by
    have hf := BitOracleStackFrame.run PrimeNonceCiphertextMachine.encryptLayout
      PrimeEncryptMachine.code E
      (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context false)
      (encryptFrame record first second samplerMod)
    rw [hePad,map_pure] at hf
    have hh := BitOracleStackFrame.run layout
      (BitOracleStackFrame.code PrimeNonceCiphertextMachine.encryptLayout PrimeEncryptMachine.code) E
      (BitOracleStackFrame.embed PrimeNonceCiphertextMachine.encryptLayout
        (PrimeEncryptMachine.start g.bits pk.bits n.bits p.bits context false)
        (encryptFrame record first second samplerMod)) frame
    rw [hf,map_pure] at hh
    exact hh
  have heBound : ce ≤ 32*E := hce.trans (Nat.mul_le_mul_left 32 hE)
  have heTail : BitOracleMachine.run code (E+D)
      (BitOracleReturnLink.embed encryptLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0))) es) =
      (fun out => (out.1,ce+out.2)) <$> tree := by
    have hhalt : ∀ out ∈ support (BitOracleMachine.run encryptCode E es), out.1.l = none := by
      rw [heRun]; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out; rfl
    have hlast : ∀ out ∈ support (BitOracleMachine.run encryptCode E es),
        ∀ last ∈ support (BitOracleMachine.run code D
          (BitOracleReturnLink.embed encryptLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0))) out.1)),
        last.1.l = none := by
      rw [heRun]; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out
      dsimp [er]
      rw [encrypt_return,hdRun]
      exact htree
    rw [BitOracleReturnLink.run _ _ _ _ encrypt_code _ _ _ hhalt hlast,heRun,pure_bind]
    dsimp [er]
    rw [encrypt_return,hdRun]
    simp only [map_eq_bind_pure_comp,Function.comp_def]
  have hgate : BitOracleMachine.run code (1+(E+D))
      (BitOracleReturnLink.embed routeLabel (some 1) rr) =
      (fun out => (out.1,3+ce+out.2)) <$> tree := by
    rw [Nat.add_comm 1,BitOracleMachine.run]
    change (do
      let firstOut ← step code (BitOracleReturnLink.embed routeLabel (some 1)
        (BitOracleStackFrame.embed layout
          (PrimeNonceCiphertextMachine.result n.bits record first second samplerMod context p.bits g.bits pk.bits false) frame))
      let lastOut ← BitOracleMachine.run code (E+D) firstOut.1
      pure (lastOut.1,firstOut.2+lastOut.2)) = _
    rw [route_return]
    simp only [pure_bind]
    change (do
      let out ← BitOracleMachine.run code (E+D)
        (BitOracleReturnLink.embed encryptLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0))) es)
      pure (out.1,3+out.2)) = _
    rw [heTail]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,Nat.add_assoc]
  obtain ⟨cr,hcr,hr⟩ := PrimeNonceCiphertextMachine.charged_bounded n (q-1) hnb
    record second samplerMod context p.bits g.bits pk.bits false
  have hrRun : BitOracleMachine.run routeCode R rs = pure (rr,cr) := by
    have hf := BitOracleStackFrame.run layout PrimeNonceCiphertextMachine.code R
      (PrimeNonceCiphertextMachine.start record first second samplerMod context p.bits g.bits pk.bits false) frame
    change BitOracleMachine.run PrimeNonceCiphertextMachine.code R
      (PrimeNonceCiphertextMachine.start record first second samplerMod context p.bits g.bits pk.bits false) = _ at hr
    rw [hr,map_pure] at hf
    exact hf
  have hrTail : BitOracleMachine.run code (R+(1+(E+D)))
      (BitOracleReturnLink.embed routeLabel (some 1) rs) =
      (fun out => (out.1,cr+3+ce+out.2)) <$> tree := by
    have hhalt : ∀ out ∈ support (BitOracleMachine.run routeCode R rs), out.1.l = none := by
      rw [hrRun]; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out; rfl
    have hlast : ∀ out ∈ support (BitOracleMachine.run routeCode R rs),
        ∀ last ∈ support (BitOracleMachine.run code (1+(E+D))
          (BitOracleReturnLink.embed routeLabel (some 1) out.1)), last.1.l = none := by
      rw [hrRun]; intro out ho; have hv := eq_of_mem_support_pure _ ho; subst out
      rw [hgate]
      intro last hl
      obtain ⟨v,hv,heq⟩ := mem_support_map_peel _ _ hl
      subst last
      exact htree v hv
    rw [BitOracleReturnLink.run _ _ _ _ route_code _ _ _ hhalt hlast,hrRun,pure_bind,hgate]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,Nat.add_assoc]
  refine ⟨fun c e z0 z1 => 3+cr+3+ce+cd c e z0 z1,?_,?_⟩
  · intro c hc e heLen z0 hz0 z1 hz1
    have hdBound := hcd c hc e heLen z0 hz0 z1 hz1
    change cr ≤ 6*R at hcr
    change 3+cr+3+ce+cd c e z0 z1 ≤ 3+6*R+(3+32*E+PrimeTranscriptDraws.cost slack q)
    clear hd hce he he' hePad heRun hdRun heTail hgate hr hrRun hrTail htree
    omega
  · change BitOracleMachine.run code (1+R+(1+E+D))
      (start (inputWords record first second samplerMod context p.bits g.bits pk.bits frame)) = _
    rw [show 1+R+(1+E+D) = (R+(1+(E+D)))+1 by omega,BitOracleMachine.run,input_entry]
    simp only [pure_bind]
    change (do
      let out ← BitOracleMachine.run code (R+(1+(E+D)))
        (BitOracleReturnLink.embed routeLabel (some 1) rs)
      pure (out.1,3+out.2)) = _
    rw [hrTail]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    dsimp [tree,output,record,first]
    simp only [bind_assoc,pure_bind,Nat.add_assoc]

#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
