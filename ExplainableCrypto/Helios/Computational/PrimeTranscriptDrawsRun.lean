import ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachineRun
import ExplainableCrypto.Helios.Computational.TranscriptScalarSaveRun

/-! Exact four-draw execution and a derived aggregate charge. -/
namespace ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- One of the fixed controller's first three phases, linked to an actual
halting suffix. The public four-draw theorem supplies the suffix equations and
derives each empty destination from the preceding state. -/
private theorem phase_then (slack q : Nat) (hq : 0 < q)
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (phase : Fin 3) (extra : Fin 3 → List Bool) (hempty : extra phase = [])
    (fuel : Nat) (next : List Bool → OracleComp spec (Config × Nat))
    (hn : ∀ bits, BitOracleMachine.run code fuel
      (BitOracleReturnLink.embed (sampleLabel ⟨phase.val+1,by omega⟩) (sampleReturn ⟨phase.val+1,by omega⟩)
        (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
          first second samplerMod context modulus g pk vote
          (Function.update extra phase (uniformNatEncode (bitsValue bits % q))))) = next bits)
    (hh : ∀ bits, ∀ out ∈ support (next bits), out.1.l = none) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = q.size+slack →
        charge bits ≤ PrimeHonestTranscriptMachine.cost slack q+saveCost q) ∧
      BitOracleMachine.run code (PrimeHonestTranscriptMachine.clock slack q+saveClock q+fuel)
        (BitOracleReturnLink.embed (sampleLabel ⟨phase.val,by omega⟩) (sampleReturn ⟨phase.val,by omega⟩)
          (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
            first second samplerMod context modulus g pk vote extra)) = (do
        let bits ← CoinWordLoader.word (q.size+slack)
        let out ← next bits
        pure (out.1,charge bits+out.2)) := by
  classical
  let word := fun bits : List Bool => uniformNatEncode (bitsValue bits % q)
  let frame := saveFrame phase alpha beta nonce (SamplerOperands.input slack q [])
    first second samplerMod context modulus g pk vote extra
  have hw (bits : List Bool) : (word bits).length ≤ scalarWidth q := by
    dsimp [word,scalarWidth]
    rw [uniformNatEncode_length]
    have h := Nat.size_le_size (show bitsValue bits % q ≤ q-1 by
      have := Nat.mod_lt (bitsValue bits) hq; omega)
    omega
  choose d hd hdRun using fun bits => TranscriptScalarSave.charged_bounded phase
    (word bits) q.bits frame (scalarWidth q) (hw bits)
  change ∀ bits, BitOracleMachine.run (TranscriptScalarSave.code phase) (saveClock q)
    (TranscriptScalarSave.start phase (word bits) q.bits frame) =
    pure (TranscriptScalarSave.result phase (word bits) frame,d bits) at hdRun
  obtain ⟨c,hc,hRun⟩ := PrimeHonestTranscriptMachine.charged slack q hq
    alpha beta nonce first second samplerMod context modulus g pk vote extra
  have hsave (bits : List Bool) : BitOracleMachine.run code (saveClock q+fuel)
      (BitOracleReturnLink.embed (sampleLabel ⟨phase.val,by omega⟩) (sampleReturn ⟨phase.val,by omega⟩)
        (PrimeHonestTranscriptMachine.result (word bits) q.bits alpha beta nonce
          (SamplerOperands.input slack q []) first second samplerMod context modulus g pk vote extra)) =
      (fun out => (out.1,d bits+out.2)) <$> next bits := by
    rw [save_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hempty]
    have ha : ∀ out ∈ support (BitOracleMachine.run (TranscriptScalarSave.code phase) (saveClock q)
        (TranscriptScalarSave.start phase (word bits) q.bits frame)), out.1.l = none := by
      rw [hdRun bits]
      intro out ho
      have he := eq_of_mem_support_pure _ ho
      subst out
      rfl
    have hb : ∀ out ∈ support (BitOracleMachine.run (TranscriptScalarSave.code phase) (saveClock q)
        (TranscriptScalarSave.start phase (word bits) q.bits frame)),
        ∀ last ∈ support (BitOracleMachine.run code fuel
          (BitOracleReturnLink.embed (saveLabel phase) (some (saveReturn phase)) out.1)), last.1.l = none := by
      rw [hdRun bits]
      intro out ho
      have he := eq_of_mem_support_pure _ ho
      subst out
      change ∀ last ∈ support (BitOracleMachine.run code fuel
        (BitOracleReturnLink.embed (saveLabel phase) (some (saveReturn phase))
          (TranscriptScalarSave.result phase (word bits) frame))), last.1.l = none
      dsimp [frame]
      rw [save_return,hn bits]
      exact hh bits
    rw [BitOracleReturnLink.run _ _ _ _ (save_code phase) _ _ _ ha hb,hdRun bits,pure_bind]
    dsimp [frame]
    rw [save_return,hn bits]
    simp only [map_eq_bind_pure_comp,Function.comp_def]
  have ha : ∀ out ∈ support (BitOracleMachine.run PrimeHonestTranscriptMachine.code
      (PrimeHonestTranscriptMachine.clock slack q)
      (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
        first second samplerMod context modulus g pk vote extra)), out.1.l = none := by
    rw [hRun]
    intro out ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rfl
  have hr : sampleReturn ⟨phase.val,by omega⟩ = some (saveLabel phase 0) := by
    simp [sampleReturn,phase.isLt]
  have hb : ∀ out ∈ support (BitOracleMachine.run PrimeHonestTranscriptMachine.code
      (PrimeHonestTranscriptMachine.clock slack q)
      (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
        first second samplerMod context modulus g pk vote extra)),
      ∀ last ∈ support (BitOracleMachine.run code (saveClock q+fuel)
        (BitOracleReturnLink.embed (sampleLabel ⟨phase.val,by omega⟩) (some (saveLabel phase 0)) out.1)),
        last.1.l = none := by
    rw [hRun]
    intro out ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rw [← hr,hsave bits]
    intro last hl
    obtain ⟨v,hv,rfl⟩ := mem_support_map_peel _ _ hl
    exact hh bits v hv
  refine ⟨fun bits => c bits+d bits,?_,?_⟩
  · intro bits hbits
    exact Nat.add_le_add (hc bits hbits) (hd bits)
  · rw [Nat.add_assoc,hr,BitOracleReturnLink.run _ _ _ _
      (fun l => by rw [← hr]; exact sample_code _ l) _ _ _ ha hb,hRun]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    apply bind_congr
    intro bits
    rw [← hr,hsave bits]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,Nat.add_assoc]

/-- Execute the exact four successive simulator scalar draws and their three
consumed saves, preserving the statement and complete caller frame. -/
theorem charged (slack q : Nat) (hq : 0 < q)
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    ∃ charge : List Bool → List Bool → List Bool → List Bool → Nat,
      (∀ c, c.length = q.size+slack → ∀ e, e.length = q.size+slack →
        ∀ z0, z0.length = q.size+slack → ∀ z1, z1.length = q.size+slack →
          charge c e z0 z1 ≤ cost slack q) ∧
      BitOracleMachine.run code (clock slack q)
        (start alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod context modulus g pk vote) = (do
        let c ← CoinWordLoader.word (q.size+slack)
        let e ← CoinWordLoader.word (q.size+slack)
        let z0 ← CoinWordLoader.word (q.size+slack)
        let z1 ← CoinWordLoader.word (q.size+slack)
        pure (result (uniformNatEncode (bitsValue c % q)) (uniformNatEncode (bitsValue e % q))
          (uniformNatEncode (bitsValue z0 % q)) (uniformNatEncode (bitsValue z1 % q))
          q.bits alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod context modulus g pk vote,
          charge c e z0 z1)) := by
  classical
  have cast0 : (⟨(0 : Fin 3).val,by decide⟩ : Fin 4) = 0 := by decide
  have cast1 : (⟨(1 : Fin 3).val,by decide⟩ : Fin 4) = 1 := by decide
  have cast2 : (⟨(2 : Fin 3).val,by decide⟩ : Fin 4) = 2 := by decide
  let word := fun bits : List Bool => uniformNatEncode (bitsValue bits % q)
  let S := PrimeHonestTranscriptMachine.clock slack q
  let T := saveClock q
  let out := fun c e z0 z1 : List Bool =>
    result (word c) (word e) (word z0) (word z1) q.bits alpha beta nonce
      (SamplerOperands.input slack q []) first second samplerMod context modulus g pk vote
  choose d3 hd3 he3 using fun c e z0 : List Bool =>
    PrimeHonestTranscriptMachine.charged slack q hq alpha beta nonce first second samplerMod
      context modulus g pk vote ![word c,word e,word z0]
  have h3 (c e z0 : List Bool) : BitOracleMachine.run code S
      (BitOracleReturnLink.embed (sampleLabel 3) (sampleReturn 3)
        (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
          first second samplerMod context modulus g pk vote ![word c,word e,word z0])) =
      (fun z1 => (out c e z0 z1,d3 c e z0 z1)) <$> CoinWordLoader.word (q.size+slack) := by
    change BitOracleMachine.run code S (BitOracleReturnLink.embed (sampleLabel 3) none _) = _
    rw [BitOracleReturnLink.rename_run _ _ _ (sample_code 3),he3 c e z0]
    simp only [Functor.map_map]
    rfl
  have h2 (c e : List Bool) := phase_then slack q hq alpha beta nonce first second samplerMod
    context modulus g pk vote 2 ![word c,word e,[]] (by rfl) S
    (fun z0 => (fun z1 => (out c e z0 z1,d3 c e z0 z1)) <$> CoinWordLoader.word (q.size+slack))
    (by
      intro z0
      have hu : Function.update ![word c,word e,[]] (2 : Fin 3) (word z0) = ![word c,word e,word z0] := by
        funext k; fin_cases k <;> rfl
      change BitOracleMachine.run code S (BitOracleReturnLink.embed (sampleLabel 3) (sampleReturn 3)
        (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
          first second samplerMod context modulus g pk vote (Function.update ![word c,word e,[]] 2 (word z0)))) = _
      rw [hu]
      exact h3 c e z0)
    (by
      intro z0 v hv
      obtain ⟨z1,_,rfl⟩ := mem_support_map_peel _ _ hv
      rfl)
  choose d2 hd2 he2 using h2
  have h1 (c : List Bool) := phase_then slack q hq alpha beta nonce first second samplerMod
    context modulus g pk vote 1 ![word c,[],[]] (by rfl) (S+T+S)
    (fun e => do
      let z0 ← CoinWordLoader.word (q.size+slack)
      let z1 ← CoinWordLoader.word (q.size+slack)
      pure (out c e z0 z1,d2 c e z0+d3 c e z0 z1))
    (by
      intro e
      have hu : Function.update ![word c,[],[]] (1 : Fin 3) (word e) = ![word c,word e,[]] := by
        funext k; fin_cases k <;> rfl
      change BitOracleMachine.run code (S+T+S) (BitOracleReturnLink.embed (sampleLabel 2) (sampleReturn 2)
        (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
          first second samplerMod context modulus g pk vote (Function.update ![word c,[],[]] 1 (word e)))) = _
      rw [hu]
      simpa only [cast2,S,T,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def] using he2 c e)
    (by
      intro e v hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨z0,_,hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨z1,_,hv⟩ := hv
      have he := eq_of_mem_support_pure _ hv
      subst v
      rfl)
  choose d1 hd1 he1 using h1
  obtain ⟨d0,hd0,he0⟩ := phase_then slack q hq alpha beta nonce first second samplerMod
    context modulus g pk vote 0 (fun _ => []) (by rfl) (S+T+(S+T+S))
    (fun c => do
      let e ← CoinWordLoader.word (q.size+slack)
      let z0 ← CoinWordLoader.word (q.size+slack)
      let z1 ← CoinWordLoader.word (q.size+slack)
      pure (out c e z0 z1,d1 c e+(d2 c e z0+d3 c e z0 z1)))
    (by
      intro c
      have hu : Function.update (fun _ : Fin 3 => []) 0 (word c) = ![word c,[],[]] := by
        funext k; fin_cases k <;> rfl
      change BitOracleMachine.run code (S+T+(S+T+S)) (BitOracleReturnLink.embed (sampleLabel 1) (sampleReturn 1)
        (PrimeHonestTranscriptMachine.start alpha beta nonce (SamplerOperands.input slack q [])
          first second samplerMod context modulus g pk vote (Function.update (fun _ => []) 0 (word c)))) = _
      rw [hu]
      simpa only [cast1,S,T,bind_assoc,pure_bind] using he1 c)
    (by
      intro c v hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨e,_,hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨z0,_,hv⟩ := hv
      rw [mem_support_bind_iff] at hv
      obtain ⟨z1,_,hv⟩ := hv
      have he := eq_of_mem_support_pure _ hv
      subst v
      rfl)
  refine ⟨fun c e z0 z1 => d0 c+(d1 c e+(d2 c e z0+d3 c e z0 z1)),?_,?_⟩
  · intro c hc e he z0 hz0 z1 hz1
    have h0 := hd0 c hc
    have h1 := hd1 c e he
    have h2 := hd2 c e z0 hz0
    have h3 := hd3 c e z0 z1 hz1
    change d0 c+(d1 c e+(d2 c e z0+d3 c e z0 z1)) ≤ _
    unfold cost
    omega
  · have hclock : clock slack q = S+T+(S+T+(S+T+S)) := by unfold clock; dsimp [S,T]; omega
    rw [hclock]
    change BitOracleMachine.run code _ (BitOracleReturnLink.embed (sampleLabel 0) (sampleReturn 0) _) = _
    simpa only [cast0,S,T,bind_assoc,pure_bind,out,word] using he0

#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
