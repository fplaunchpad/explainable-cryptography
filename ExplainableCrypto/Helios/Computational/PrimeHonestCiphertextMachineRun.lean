import ExplainableCrypto.Helios.Computational.PrimeHonestInputMachineRun
import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCallerSource
import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine

/-! Full initialized execution with derived component and entry costs. -/

namespace ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem caller_gate (fuel : Nat) (modulus g pk record context : List Bool) (vote : Bool) :
    BitOracleMachine.run code (1+fuel)
      (BitOracleReturnLink.embed inputLabel (some 0)
        (PrimeHonestInputMachine.result modulus g pk record context vote)) =
    (fun out => (BitOracleReturnLink.embed callerLabel none out.1,3+out.2)) <$>
      BitOracleMachine.run PrimeNonceCiphertextCaller.code fuel
        (PrimeNonceCiphertextCaller.start g pk modulus record context vote) := by
  rw [Nat.add_comm 1,BitOracleMachine.run,input_return]
  simp only [pure_bind]
  rw [BitOracleReturnLink.rename_run _ _ _ caller_code]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

/-- Initialization and entry are executed before the exact existing caller;
the full query tree and initializer/entry charge are preserved. -/
theorem linked_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (slack : Nat) (vote : Bool) (saved : List Bool) :
    ∃ c ≤ 32*PrimeHonestInputMachine.clock (PrimeHonestInputMachine.input g pk slack vote saved),
      BitOracleMachine.run code
        (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
        (start (PrimeHonestInputMachine.input g pk slack vote saved)) =
      (fun out => (BitOracleReturnLink.embed callerLabel none out.1,c+3+out.2)) <$>
        BitOracleMachine.run PrimeNonceCiphertextCaller.code (PrimeNonceCiphertextCaller.clock slack p q)
          (PrimeNonceCiphertextCaller.start (primeGroupCoordinate g).val.bits
            (primeGroupCoordinate pk).val.bits p.bits (SamplerOperands.input slack q [])
            (PrimeHonestInputMachine.input g pk slack vote saved) vote) := by
  obtain ⟨c,hc,he⟩ := PrimeHonestInputMachine.charged g pk slack vote saved
  obtain ⟨d,_,hd⟩ := PrimeNonceCiphertextCaller.caller_run slack p q
    (primeGroupCoordinate g).val (primeGroupCoordinate pk).val
    (Fact.out : q.Prime).two_le (Fact.out : p.Prime).two_le
    (primeGroupCoordinate g).val_lt (primeGroupCoordinate pk).val_lt
    (PrimeHonestInputMachine.input g pk slack vote saved) vote
  have hh : ∀ out ∈ support (BitOracleMachine.run PrimeHonestInputMachine.code
      (PrimeHonestInputMachine.clock (PrimeHonestInputMachine.input g pk slack vote saved))
      (PrimeHonestInputMachine.start (PrimeHonestInputMachine.input g pk slack vote saved))),
      out.1.l = none := by
    rw [he]
    intro out ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rfl
  have hhalt : ∀ out ∈ support (BitOracleMachine.run PrimeHonestInputMachine.code
      (PrimeHonestInputMachine.clock (PrimeHonestInputMachine.input g pk slack vote saved))
      (PrimeHonestInputMachine.start (PrimeHonestInputMachine.input g pk slack vote saved))),
      ∀ last ∈ support (BitOracleMachine.run code (1+PrimeNonceCiphertextCaller.clock slack p q)
        (BitOracleReturnLink.embed inputLabel (some 0) out.1)), last.1.l = none := by
    rw [he]
    intro out ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rw [caller_gate,hd]
    intro last hl
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def] at hl
    rw [mem_support_bind_iff] at hl
    obtain ⟨a,_,hl⟩ := hl
    rw [mem_support_bind_iff] at hl
    obtain ⟨b,_,hl⟩ := hl
    have hv := eq_of_mem_support_pure _ hl
    subst last
    rfl
  refine ⟨c,hc,?_⟩
  simp only [clock,Nat.add_assoc,start]
  rw [BitOracleReturnLink.run _ _ _ _ input_code _ _ _ hh hhalt,he,pure_bind,caller_gate]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

/-- Complete initialized execution, with both actual sequential coin words,
full retained state and the derived sum of initializer, entry and caller costs. -/
theorem charged {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (slack : Nat) (vote : Bool) (saved : List Bool) :
    ∃ charge : List Bool → List Bool → Nat,
      (∀ a, a.length = PrimeNonceMachine.sampleWidth slack q →
        ∀ b, b.length = PrimeNonceMachine.sampleWidth slack q →
          charge a b ≤ cost (PrimeHonestInputMachine.input g pk slack vote saved) slack p q) ∧
      BitOracleMachine.run code
        (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
        (start (PrimeHonestInputMachine.input g pk slack vote saved)) = (do
        let a ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        let b ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        pure (BitOracleReturnLink.embed callerLabel none
          (PrimeNonceCiphertextCaller.numericResult slack p q (primeGroupCoordinate g).val
            (primeGroupCoordinate pk).val (PrimeHonestInputMachine.input g pk slack vote saved) vote a b),
          charge a b)) := by
  obtain ⟨c,hc,he⟩ := linked_run g pk slack vote saved
  obtain ⟨d,hd,hr⟩ := PrimeNonceCiphertextCaller.caller_run slack p q
    (primeGroupCoordinate g).val (primeGroupCoordinate pk).val
    (Fact.out : q.Prime).two_le (Fact.out : p.Prime).two_le
    (primeGroupCoordinate g).val_lt (primeGroupCoordinate pk).val_lt
    (PrimeHonestInputMachine.input g pk slack vote saved) vote
  refine ⟨fun a b => c+3+d a b,?_,?_⟩
  · intro a ha b hb
    have hd' := hd a ha b hb
    change c+3+d a b ≤ _
    unfold cost
    omega
  · rw [he,hr]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

#print axioms linked_run
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine
