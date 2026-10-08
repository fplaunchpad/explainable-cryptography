import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptSource
import ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachineRun
import ExplainableCrypto.Helios.Computational.PrimeFullFieldSource
import ExplainableCrypto.Helios.Computational.PrimeEncryptMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
open OracleComp OracleSpec BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
attribute [local irreducible] BitOracleMachine.run

/-- The actual other-component statement at the retained second nonce. Only
its four transcript scalars are freshly sampled; every prior word stays resident. -/
def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  result (primeGroupCoordinate (encryptWith g pk out.1.2 (voteScalar false)).1).val.bits
    (primeGroupCoordinate (encryptWith g pk out.1.2 (voteScalar false)).2).val.bits
    out.1.2.val.bits (scalarEncode cs.1) (scalarEncode cs.2.1)
    (scalarEncode cs.2.2.1) (scalarEncode cs.2.2.2) q.bits
    (PrimeSecondTranscriptSource.words slack g pk vote s live out)

/-- All fifty old words, including p0, both nonces, original vote/raw input and
updated saved state, are preserved literally. -/
theorem source_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (k : Fin 50) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ =
      PrimeSecondTranscriptSource.words slack g pk vote s live out k := by
  simp only [sourceResult,result,dif_pos k.isLt]

/-- Fresh output fields identify the actual p1 ciphertext and four scalar draws. -/
theorem source_fields (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    let cfg := sourceResult slack g pk vote s live out cs
    cfg.stk 50 = (primeGroupCoordinate (honestProofStatement g pk (false,out.1.2)).ciphertext.1).val.bits ∧
    cfg.stk 51 = (primeGroupCoordinate (honestProofStatement g pk (false,out.1.2)).ciphertext.2).val.bits ∧
    cfg.stk 52 = out.1.2.val.bits ∧ cfg.stk 53 = [false] ∧
    cfg.stk 54 = scalarEncode cs.1 ∧ cfg.stk 55 = scalarEncode cs.2.1 ∧
    cfg.stk 56 = scalarEncode cs.2.2.1 ∧ cfg.stk 57 = scalarEncode cs.2.2.2 ∧ cfg.stk 58 = q.bits :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem residue_pow (a : ZMod p) (n : Nat) :
    (a^n).val = a.val^n%p := by
  simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using (ZMod.val_natCast p (a.val^n))

private theorem false_coordinates (g pk : PrimeGroup p q) (r : ZMod q) :
    ((primeGroupCoordinate (encryptWith g pk r (voteScalar false)).1).val.bits,
      (primeGroupCoordinate (encryptWith g pk r (voteScalar false)).2).val.bits) =
    (((primeGroupCoordinate g).val^r.val%p).bits,
      ((primeGroupCoordinate pk).val^r.val%p).bits) := by
  have h := primeGroup_encrypt_coordinates g pk r (voteScalar false)
  have h' := congrArg (fun pair : ZMod p × ZMod p => (pair.1.val.bits,pair.2.val.bits)) h
  simpa only [voteScalar,Bool.false_eq_true,ite_false,ZMod.val_zero,pow_zero,one_mul,residue_pow] using h'

private theorem scalar_cast_word (a : List Bool) :
    scalarEncode (bitsValue a : ZMod q) = uniformNatEncode (bitsValue a % q) := by
  simp only [scalarEncode,ZMod.val_natCast]

/-- Actual execution at the second-component source boundary, including four
successive fresh coin words and their derived branch charge. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    ∃ charge : List Bool → List Bool → List Bool → List Bool → Nat,
      (∀ a, a.length = q.size+slack → ∀ b, b.length = q.size+slack →
        ∀ c, c.length = q.size+slack → ∀ d, d.length = q.size+slack →
        charge a b c d ≤ cost slack p q) ∧
      BitOracleMachine.run code (clock slack p q)
        (start (PrimeSecondTranscriptSource.words slack g pk vote s live out)) = (do
        let a ← CoinWordLoader.word (q.size+slack)
        let b ← CoinWordLoader.word (q.size+slack)
        let c ← CoinWordLoader.word (q.size+slack)
        let d ← CoinWordLoader.word (q.size+slack)
        pure (sourceResult slack g pk vote s live out
          ((bitsValue a : ZMod q),(bitsValue b : ZMod q),(bitsValue c : ZMod q),(bitsValue d : ZMod q)),
          charge a b c d)) := by
  let old := PrimeSecondTranscriptSource.words slack g pk vote s live out
  let ctx := (ballotBothCachesBitCodec p q).encode
    (PrimeProgramRepackSource.nextState g pk vote s out,live)
  obtain ⟨charge,hc,he⟩ := charged slack p q (primeGroupCoordinate g).val
    (primeGroupCoordinate pk).val out.1.2.val (Fact.out : p.Prime).two_le
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
    (scalarEncode out.1.1) (q-1).bits ctx (frame old)
  have hp := PrimeSecondTranscriptSource.source_presentation slack g pk vote s live out
  change old = inputWords (SamplerOperands.input slack q []) (uniformNatEncode out.1.2.val)
    (scalarEncode out.1.1) (q-1).bits ctx p.bits (primeGroupCoordinate g).val.bits
    (primeGroupCoordinate pk).val.bits (frame old) at hp
  rw [←hp] at he
  have ha := congrArg Prod.fst (false_coordinates g pk out.1.2)
  have hb := congrArg Prod.snd (false_coordinates g pk out.1.2)
  dsimp only at ha hb
  rw [←ha,←hb] at he
  refine ⟨charge,hc,?_⟩
  rw [he]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  apply bind_congr
  intro c
  apply bind_congr
  intro d
  simp only [sourceResult,scalar_cast_word,old]

/-- The original p1 request reuses r2 and executes only the four fresh full-field
draws. No nonce pair is resampled and no old saved record is re-extracted. -/
theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    Prod.fst <$> BitOracleMachine.run code (clock slack p q)
      (start (PrimeSecondTranscriptSource.words slack g pk vote s live out)) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote s live out <$>
          runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote s live out
  rw [he]
  let W := (fun bits => uniformNatEncode (bitsValue bits % q)) <$>
    CoinWordLoader.word (q.size+slack)
  have hW := PrimeFullFieldSource.scalar_word_source q slack
  change W = _ at hW
  calc
    _ = (do
      let c ← W
      let e ← W
      let z0 ← W
      let z1 ← W
      pure (result
        (primeGroupCoordinate (encryptWith g pk out.1.2 (voteScalar false)).1).val.bits
        (primeGroupCoordinate (encryptWith g pk out.1.2 (voteScalar false)).2).val.bits
        out.1.2.val.bits c e z0 z1 q.bits
        (PrimeSecondTranscriptSource.words slack g pk vote s live out))) := by
      simp only [W,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,
        sourceResult,scalar_cast_word]
    _ = _ := by
      rw [hW]
      simp only [PrimeFullFieldSource.drawTranscriptScalars,runFairBitUniform,simulateQ_bind,
        simulateQ_pure,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,sourceResult]

/-- Every supported branch of the actual source run halts within its derived
charge bound; this discharges the raw caller's probabilistic return obligation. -/
theorem run_support_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q)) :
    ∀ last ∈ support (BitOracleMachine.run code (clock slack p q)
      (start (PrimeSecondTranscriptSource.words slack g pk vote s live out))),
      last.1.l = none ∧ last.2 ≤ cost slack p q := by
  obtain ⟨charge,hc,he⟩ := charged_source slack g pk vote s live out
  rw [he]
  intro last hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨a,ha,hl⟩ := hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨b,hb,hl⟩ := hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨c,hc',hl⟩ := hl
  rw [mem_support_bind_iff] at hl
  obtain ⟨d,hd,hl⟩ := hl
  have heq := eq_of_mem_support_pure _ hl
  subst last
  exact ⟨rfl,hc a (CoinWordLoader.word_length _ _ ha)
    b (CoinWordLoader.word_length _ _ hb) c (CoinWordLoader.word_length _ _ hc')
    d (CoinWordLoader.word_length _ _ hd)⟩

#print axioms charged_source
#print axioms execution_source
#print axioms run_support_source
#print axioms source_retained
#print axioms source_fields
end ExplainableCrypto.Helios.Computational.PrimeSecondTranscriptMachine
