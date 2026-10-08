import ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
import ExplainableCrypto.Helios.Computational.PrimeNonceSamplingSource
import ExplainableCrypto.Helios.Computational.PrimeNoncePairTransportRun

namespace ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem entry_code (l : Fin PrimeNoncePairTransport.size) : code (entryLabel l) =
    BitOracleReturnLink.command entryLabel (some (firstLabel 0)) (PrimeNoncePairTransport.code l) := by
  fin_cases l <;> rfl
private theorem first_code (l : Fin 71) : code (firstLabel l) =
    BitOracleReturnLink.command firstLabel (some 0) (PrimeNonceMachine.sampleCode l) := by
  fin_cases l <;> rfl
private theorem between_code (l : Fin PrimeNoncePairTransport.size) : code (betweenLabel l) =
    BitOracleReturnLink.command betweenLabel (some (secondLabel 0)) (PrimeNoncePairTransport.code l) := by
  fin_cases l <;> rfl
private theorem second_code (l : Fin 71) : code (secondLabel l) =
    BitOracleReturnLink.command secondLabel none (PrimeNonceMachine.sampleCode l) := by
  fin_cases l <;> rfl

private theorem second_run (fuel : Nat) (cfg : Config 11 71 3) :
    run code fuel (BitOracleReturnLink.embed secondLabel none cfg) =
      (fun out => (BitOracleReturnLink.embed secondLabel none out.1,out.2)) <$>
        run PrimeNonceMachine.sampleCode fuel cfg :=
  BitOracleReturnLink.rename_run _ _ _ second_code fuel cfg

private theorem result_eq (record first second modulus context : List Bool) :
    BitOracleReturnLink.embed secondLabel none
      (PrimeNonceMachine.sampleOutput second modulus ![record,first,context]) =
      result record first second modulus context := by
  rfl

private theorem gate (record modulus nonce context : List Bool) :
    step code (BitOracleReturnLink.embed firstLabel (some 0)
      (PrimeNonceMachine.sampleOutput nonce modulus ![record,[],context])) =
      pure (BitOracleReturnLink.embed betweenLabel (some (secondLabel 0))
        (PrimeNoncePairTransport.betweenStart record modulus nonce context),3) := by
  rfl

private theorem ready_second (record nonce context : List Bool) :
    BitOracleReturnLink.embed betweenLabel (some (secondLabel 0))
      (PrimeNoncePairTransport.ready record nonce context) =
      BitOracleReturnLink.embed secondLabel none
        (PrimeNonceMachine.sampleStart record ![record,nonce,context]) := by
  change (⟨some (secondLabel 0),0,_⟩ : Config 11 size 3) = ⟨some (secondLabel 0),0,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

private theorem ready_first (record context : List Bool) :
    BitOracleReturnLink.embed entryLabel (some (firstLabel 0))
      (PrimeNoncePairTransport.ready record [] context) =
      BitOracleReturnLink.embed firstLabel (some 0)
        (PrimeNonceMachine.sampleStart record ![record,[],context]) := by
  change (⟨some (firstLabel 0),0,_⟩ : Config 11 size 3) = ⟨some (firstLabel 0),0,_⟩
  congr 1
  funext k; fin_cases k <;> rfl

private def nonceWord (q : Nat) (bits : List Bool) : List Bool :=
  uniformNatEncode (bitsValue bits % (q-1)+1)

private theorem nonce_width (q : Nat) (hq : 2 ≤ q) (bits : List Bool) :
    (nonceWord q bits).length ≤ nonceWidth q := by
  have hm := Nat.mod_lt (bitsValue bits) (show 0 < q-1 by omega)
  have hs := Nat.size_le_size (show bitsValue bits % (q-1)+1 ≤ q-1 by omega)
  simp only [nonceWord,uniformNatEncode_length,nonceWidth]
  omega


private theorem between_linked (slack q : Nat) (hq : 2 ≤ q) (nonce context : List Bool) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = PrimeNonceMachine.sampleWidth slack q → charge bits ≤
        PrimeNoncePairTransport.betweenCost (SamplerOperands.input slack q []) (q-1).bits nonce+
          PrimeNonceMachine.sampleCost slack q) ∧
      run code (PrimeNoncePairTransport.betweenClock (SamplerOperands.input slack q []) (q-1).bits nonce+
          PrimeNonceMachine.sampleClock slack q)
        (BitOracleReturnLink.embed betweenLabel (some (secondLabel 0))
          (PrimeNoncePairTransport.betweenStart (SamplerOperands.input slack q []) (q-1).bits nonce context)) =
        (fun bits => (result (SamplerOperands.input slack q []) nonce (nonceWord q bits) (q-1).bits context,
          charge bits)) <$> CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q) := by
  obtain ⟨c,hc,he⟩ := PrimeNoncePairTransport.between_run (SamplerOperands.input slack q []) (q-1).bits nonce context
  obtain ⟨cs,hcs,hs⟩ := PrimeNonceMachine.sample_source slack q hq
    ![SamplerOperands.input slack q [],nonce,context]
  have tail : run code (PrimeNonceMachine.sampleClock slack q)
      (BitOracleReturnLink.embed betweenLabel (some (secondLabel 0))
        (PrimeNoncePairTransport.ready (SamplerOperands.input slack q []) nonce context)) =
      (fun bits => (result (SamplerOperands.input slack q []) nonce (nonceWord q bits) (q-1).bits context,
        cs bits)) <$> CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q) := by
    rw [ready_second,second_run,hs]
    simp only [Functor.map_map,result_eq,nonceWord]
  have hh : ∀ out ∈ support (run PrimeNoncePairTransport.code
      (PrimeNoncePairTransport.betweenClock (SamplerOperands.input slack q []) (q-1).bits nonce)
      (PrimeNoncePairTransport.betweenStart (SamplerOperands.input slack q []) (q-1).bits nonce context)),
      out.1.l = none := by
    rw [he]; intro out ho
    have hv := eq_of_mem_support_pure _ ho
    subst out; rfl
  have ht : ∀ out ∈ support (run PrimeNoncePairTransport.code
      (PrimeNoncePairTransport.betweenClock (SamplerOperands.input slack q []) (q-1).bits nonce)
      (PrimeNoncePairTransport.betweenStart (SamplerOperands.input slack q []) (q-1).bits nonce context)),
      ∀ last ∈ support (run code (PrimeNonceMachine.sampleClock slack q)
        (BitOracleReturnLink.embed betweenLabel (some (secondLabel 0)) out.1)), last.1.l = none := by
    rw [he]; intro out ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rw [tail]; intro last hl
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ hl
    rfl
  refine ⟨fun bits => c+cs bits,?_,?_⟩
  · intro bits hb
    exact Nat.add_le_add hc (hcs bits hb)
  · rw [BitOracleReturnLink.run _ _ _ _ between_code _ _ _ hh ht,he,pure_bind,tail]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

private theorem after_first (slack q : Nat) (hq : 2 ≤ q) (bits₀ context : List Bool) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = PrimeNonceMachine.sampleWidth slack q → charge bits ≤
        3+betweenCostBound slack q+PrimeNonceMachine.sampleCost slack q) ∧
      run code (1+betweenBound slack q+PrimeNonceMachine.sampleClock slack q)
        (BitOracleReturnLink.embed firstLabel (some 0)
          (PrimeNonceMachine.sampleOutput (nonceWord q bits₀) (q-1).bits
            ![SamplerOperands.input slack q [],[],context])) =
        (fun bits => (result (SamplerOperands.input slack q []) (nonceWord q bits₀)
          (nonceWord q bits) (q-1).bits context,charge bits)) <$>
            CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q) := by
  obtain ⟨c,hc,he⟩ := between_linked slack q hq (nonceWord q bits₀) context
  have hn := nonce_width q hq bits₀
  have ht : PrimeNoncePairTransport.betweenClock (SamplerOperands.input slack q []) (q-1).bits
      (nonceWord q bits₀) ≤ betweenBound slack q := by
    simp only [PrimeNoncePairTransport.betweenClock,betweenBound,List.length_replicate]
    omega
  have hb : PrimeNoncePairTransport.betweenCost (SamplerOperands.input slack q []) (q-1).bits
      (nonceWord q bits₀) ≤ betweenCostBound slack q := by
    simp only [PrimeNoncePairTransport.betweenCost,betweenCostBound,List.length_replicate]
    omega
  have hh : ∀ out ∈ support (run code
      (PrimeNoncePairTransport.betweenClock (SamplerOperands.input slack q []) (q-1).bits (nonceWord q bits₀)+
        PrimeNonceMachine.sampleClock slack q)
      (BitOracleReturnLink.embed betweenLabel (some (secondLabel 0))
        (PrimeNoncePairTransport.betweenStart (SamplerOperands.input slack q []) (q-1).bits
          (nonceWord q bits₀) context))), out.1.l = none := by
    rw [he]; intro out ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rfl
  obtain ⟨extra,hextra⟩ := Nat.exists_eq_add_of_le ht
  have hp := BitOracleReturnLink.padded code _ extra _ hh
  have ht' : betweenBound slack q+PrimeNonceMachine.sampleClock slack q =
      extra+(PrimeNoncePairTransport.betweenClock (SamplerOperands.input slack q []) (q-1).bits
        (nonceWord q bits₀)+PrimeNonceMachine.sampleClock slack q) := by omega
  refine ⟨fun bits => 3+c bits,?_,?_⟩
  · intro bits hw
    have hc' := hc bits hw
    change 3+c bits ≤ _
    omega
  · rw [show 1+betweenBound slack q+PrimeNonceMachine.sampleClock slack q =
        (betweenBound slack q+PrimeNonceMachine.sampleClock slack q)+1 by omega,
      run,gate,pure_bind,ht',hp,he]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

private theorem first_linked (slack q : Nat) (hq : 2 ≤ q) (context : List Bool) :
    ∃ charge : List Bool → List Bool → Nat,
      (∀ a, a.length = PrimeNonceMachine.sampleWidth slack q →
        ∀ b, b.length = PrimeNonceMachine.sampleWidth slack q → charge a b ≤
          PrimeNonceMachine.sampleCost slack q+(3+betweenCostBound slack q+PrimeNonceMachine.sampleCost slack q)) ∧
      run code (PrimeNonceMachine.sampleClock slack q+
          (1+betweenBound slack q+PrimeNonceMachine.sampleClock slack q))
        (BitOracleReturnLink.embed firstLabel (some 0)
          (PrimeNonceMachine.sampleStart (SamplerOperands.input slack q [])
            ![SamplerOperands.input slack q [],[],context])) = (do
        let a ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        let b ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        pure (result (SamplerOperands.input slack q []) (nonceWord q a) (nonceWord q b) (q-1).bits context,
          charge a b)) := by
  obtain ⟨c,hc,he⟩ := PrimeNonceMachine.sample_source slack q hq
    ![SamplerOperands.input slack q [],[],context]
  choose tail ht htRun using fun a => after_first slack q hq a context
  simp only [nonceWord] at htRun
  have hh : ∀ out ∈ support (run PrimeNonceMachine.sampleCode (PrimeNonceMachine.sampleClock slack q)
      (PrimeNonceMachine.sampleStart (SamplerOperands.input slack q [])
        ![SamplerOperands.input slack q [],[],context])), out.1.l = none := by
    rw [he]; intro out ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rfl
  have hhalt : ∀ out ∈ support (run PrimeNonceMachine.sampleCode (PrimeNonceMachine.sampleClock slack q)
      (PrimeNonceMachine.sampleStart (SamplerOperands.input slack q [])
        ![SamplerOperands.input slack q [],[],context])),
      ∀ last ∈ support (run code (1+betweenBound slack q+PrimeNonceMachine.sampleClock slack q)
        (BitOracleReturnLink.embed firstLabel (some 0) out.1)), last.1.l = none := by
    rw [he]; intro out ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rw [htRun bits]; intro last hl
    obtain ⟨other,_,rfl⟩ := mem_support_map_peel _ _ hl
    rfl
  refine ⟨fun a b => c a+tail a b,?_,?_⟩
  · intro a ha b hb
    exact Nat.add_le_add (hc a ha) (ht a b hb)
  · rw [BitOracleReturnLink.run _ _ _ _ first_code _ _ _ hh hhalt,he]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    apply bind_congr
    intro a
    rw [htRun a]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,nonceWord]

/-- The actual pair caller preserves both independent coin words, both encoded
nonces, its public input record and private context, with a derived total charge.
Every transport and sampler return premise follows from actual execution. -/
theorem pair_run (slack q : Nat) (hq : 2 ≤ q) (context : List Bool) :
    ∃ charge : List Bool → List Bool → Nat,
      (∀ a, a.length = PrimeNonceMachine.sampleWidth slack q →
        ∀ b, b.length = PrimeNonceMachine.sampleWidth slack q → charge a b ≤ cost slack q) ∧
      run code (clock slack q) (start (SamplerOperands.input slack q []) context) = (do
        let a ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        let b ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
        pure (result (SamplerOperands.input slack q [])
          (uniformNatEncode (bitsValue a % (q-1)+1)) (uniformNatEncode (bitsValue b % (q-1)+1))
          (q-1).bits context,charge a b)) := by
  obtain ⟨c,hc,he⟩ := PrimeNoncePairTransport.entry_run (SamplerOperands.input slack q []) [] context
  obtain ⟨tail,ht,htRun⟩ := first_linked slack q hq context
  have hh : ∀ out ∈ support (run PrimeNoncePairTransport.code
      (PrimeNoncePairTransport.entryClock (SamplerOperands.input slack q []))
      (PrimeNoncePairTransport.entryStart (SamplerOperands.input slack q []) [] context)), out.1.l = none := by
    rw [he]; intro out ho
    have hv := eq_of_mem_support_pure _ ho
    subst out; rfl
  have hhalt : ∀ out ∈ support (run PrimeNoncePairTransport.code
      (PrimeNoncePairTransport.entryClock (SamplerOperands.input slack q []))
      (PrimeNoncePairTransport.entryStart (SamplerOperands.input slack q []) [] context)),
      ∀ last ∈ support (run code (PrimeNonceMachine.sampleClock slack q+
          (1+betweenBound slack q+PrimeNonceMachine.sampleClock slack q))
        (BitOracleReturnLink.embed entryLabel (some (firstLabel 0)) out.1)), last.1.l = none := by
    rw [he]; intro out ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rw [ready_first,htRun]; intro last hl
    rw [mem_support_bind_iff] at hl
    obtain ⟨a,_,hl⟩ := hl
    rw [mem_support_bind_iff] at hl
    obtain ⟨b,_,hl⟩ := hl
    have hv := eq_of_mem_support_pure _ hl
    subst last; rfl
  refine ⟨fun a b => c+tail a b,?_,?_⟩
  · intro a ha b hb
    exact Nat.add_le_add hc (ht a ha b hb)
  · rw [clock,start,BitOracleReturnLink.run _ _ _ _ entry_code _ _ _ hh hhalt,he,pure_bind,
      ready_first,htRun]
    simp only [bind_assoc,pure_bind,nonceWord]

#print axioms pair_run
end ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
