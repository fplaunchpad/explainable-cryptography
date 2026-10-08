import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCallerRun

/-! Reusable resident request entry into existing finite code. It consumes a
canonical nonce prefix, executes encryption for either vote and draws four fresh
scalars. It does not run the raw initializer or resample the nonce pair. -/
namespace ExplainableCrypto.Helios.Computational.PrimeRequestDraws
open OracleComp OracleSpec BitOracleMachine
abbrev size := PrimeHonestTranscriptCaller.size
abbrev Config := PrimeHonestTranscriptCaller.Config
abbrev code := PrimeHonestTranscriptCaller.code

def cipherStart (record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) : PrimeHonestCiphertextMachine.Config :=
  BitOracleReturnLink.embed PrimeHonestCiphertextMachine.callerLabel none
    (BitOracleReturnLink.embed PrimeNonceCiphertextCaller.routeLabel (some 0)
      (PrimeNonceCiphertextMachine.start record first second samplerMod context modulus g pk vote))

def start (record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) : Config :=
  BitOracleReturnLink.embed PrimeHonestTranscriptCaller.cipherLabel
    (some (PrimeHonestTranscriptCaller.drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
    (cipherStart record first second samplerMod context modulus g pk vote)

def entry : Fin size := 99

theorem start_entry (record first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) :
    (start record first second samplerMod context modulus g pk vote).l = some entry := rfl

def cipherClock (p q : Nat) := PrimeNonceCiphertextMachine.clock (q-1)+
  (1+PrimeEncryptMachine.clock p (q-1).size)
def cipherCost (p q : Nat) := 6*PrimeNonceCiphertextMachine.clock (q-1)+
  3+32*PrimeEncryptMachine.clock p (q-1).size
def clock (slack p q : Nat) := cipherClock p q+PrimeTranscriptDraws.clock slack q
def cost (slack p q : Nat) := cipherCost p q+PrimeTranscriptDraws.cost slack q

def cipherResult (slack p q g pk n : Nat) (second samplerMod context : List Bool)
    (vote : Bool) : PrimeHonestCiphertextMachine.Config :=
  PrimeHonestCiphertextMachine.result (g^n%p).bits
    (((pk^n%p)*(if vote then g else 1))%p).bits n.bits
    (SamplerOperands.input slack q []) (uniformNatEncode n) second samplerMod context
    p.bits g.bits pk.bits vote

def result (slack p q g pk n : Nat) (second samplerMod context : List Bool)
    (vote : Bool) (c e z0 z1 : List Bool) : Config :=
  PrimeHonestTranscriptCaller.result
    (uniformNatEncode (bitsValue c%q)) (uniformNatEncode (bitsValue e%q))
    (uniformNatEncode (bitsValue z0%q)) (uniformNatEncode (bitsValue z1%q)) q.bits
    (g^n%p).bits (((pk^n%p)*(if vote then g else 1))%p).bits n.bits
    (SamplerOperands.input slack q []) (uniformNatEncode n) second samplerMod context
    p.bits g.bits pk.bits vote

set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] BitOracleMachine.run
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- Reuse the existing nonce-routing/encryption continuation, with no nonce
sampling and no positivity premise on the supplied nonce. -/
private theorem cipher_charged (slack p q g pk n : Nat) (hp : 2 ≤ p)
    (hg : g < p) (hpk : pk < p) (hn : n < q)
    (second samplerMod context : List Bool) (vote : Bool) :
    ∃ charge ≤ cipherCost p q,
      BitOracleMachine.run PrimeHonestCiphertextMachine.code (cipherClock p q)
        (cipherStart (SamplerOperands.input slack q []) (uniformNatEncode n)
          second samplerMod context p.bits g.bits pk.bits vote) =
      pure (cipherResult slack p q g pk n second samplerMod context vote,charge) := by
  obtain ⟨charge,hc,he⟩ := PrimeNonceCiphertextCaller.continuation p g pk n (q-1)
    (by omega) (SamplerOperands.input slack q []) second samplerMod context vote hp hg hpk
  unfold cipherStart cipherClock
  rw [BitOracleReturnLink.rename_run _ _ _ PrimeHonestCiphertextMachine.caller_code,he,map_pure]
  exact ⟨charge,hc,rfl⟩

/-- One resident entry of the existing program executes encryption and four
fresh draws. Every return/halt premise and total charge follows from its code. -/
theorem charged (slack p q g pk n : Nat) (hp : 2 ≤ p)
    (hg : g < p) (hpk : pk < p) (hn : n < q)
    (second samplerMod context : List Bool) (vote : Bool) :
    ∃ charge : List Bool → List Bool → List Bool → List Bool → Nat,
      (∀ c, c.length = q.size+slack → ∀ e, e.length = q.size+slack →
        ∀ z0, z0.length = q.size+slack → ∀ z1, z1.length = q.size+slack →
          charge c e z0 z1 ≤ cost slack p q) ∧
      BitOracleMachine.run code (clock slack p q)
        (start (SamplerOperands.input slack q []) (uniformNatEncode n)
          second samplerMod context p.bits g.bits pk.bits vote) = (do
        let c ← CoinWordLoader.word (q.size+slack)
        let e ← CoinWordLoader.word (q.size+slack)
        let z0 ← CoinWordLoader.word (q.size+slack)
        let z1 ← CoinWordLoader.word (q.size+slack)
        pure (result slack p q g pk n second samplerMod context vote c e z0 z1,
          charge c e z0 z1)) := by
  classical
  obtain ⟨a,ha,he⟩ := cipher_charged slack p q g pk n hp hg hpk hn second samplerMod context vote
  obtain ⟨d,hd,ht⟩ := PrimeTranscriptDraws.charged slack q (by omega)
    (g^n%p).bits (((pk^n%p)*(if vote then g else 1))%p).bits n.bits
    (uniformNatEncode n) second samplerMod context p.bits g.bits pk.bits vote
  let initial := cipherStart (SamplerOperands.input slack q []) (uniformNatEncode n)
    second samplerMod context p.bits g.bits pk.bits vote
  let tail := PrimeTranscriptDraws.start (g^n%p).bits
    (((pk^n%p)*(if vote then g else 1))%p).bits n.bits
    (SamplerOperands.input slack q []) (uniformNatEncode n) second samplerMod context
    p.bits g.bits pk.bits vote
  have htail : ∀ out ∈ support (BitOracleMachine.run PrimeTranscriptDraws.code
      (PrimeTranscriptDraws.clock slack q) tail), out.1.l = none := by
    dsimp only [tail]
    rw [ht]
    intro out ho
    rw [mem_support_bind_iff] at ho; obtain ⟨c,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho; obtain ⟨e,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho; obtain ⟨z0,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho; obtain ⟨z1,_,ho⟩ := ho
    obtain rfl := eq_of_mem_support_pure _ ho
    rfl
  have hh : ∀ out ∈ support (BitOracleMachine.run PrimeHonestCiphertextMachine.code
      (cipherClock p q) initial), out.1.l = none := by
    dsimp only [initial]
    rw [he]
    intro out ho
    obtain rfl := eq_of_mem_support_pure _ ho
    rfl
  have hr : BitOracleReturnLink.embed PrimeHonestTranscriptCaller.cipherLabel
      (some (PrimeHonestTranscriptCaller.drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (cipherResult slack p q g pk n second samplerMod context vote) =
      BitOracleReturnLink.embed PrimeHonestTranscriptCaller.drawLabel none tail := rfl
  have hl : ∀ out ∈ support (BitOracleMachine.run PrimeHonestCiphertextMachine.code
      (cipherClock p q) initial), ∀ last ∈ support (BitOracleMachine.run code
      (PrimeTranscriptDraws.clock slack q)
      (BitOracleReturnLink.embed PrimeHonestTranscriptCaller.cipherLabel
        (some (PrimeHonestTranscriptCaller.drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
        out.1)), last.1.l = none := by
    dsimp only [initial]
    rw [he]
    intro out ho
    obtain rfl := eq_of_mem_support_pure _ ho
    rw [hr,BitOracleReturnLink.rename_run _ _ _ PrimeHonestTranscriptCaller.draw_code]
    intro last hlast
    obtain ⟨v,hv,rfl⟩ := mem_support_map_peel _ _ hlast
    change v.1.l.elim none (some ∘ PrimeHonestTranscriptCaller.drawLabel) = none
    rw [htail v hv]
    rfl
  refine ⟨fun c e z0 z1 => a+d c e z0 z1,?_,?_⟩
  · intro c hc e he z0 hz0 z1 hz1
    exact Nat.add_le_add ha (hd c hc e he z0 hz0 z1 hz1)
  · change BitOracleMachine.run PrimeHonestTranscriptCaller.code (_+_)
      (BitOracleReturnLink.embed PrimeHonestTranscriptCaller.cipherLabel _ initial) = _
    rw [BitOracleReturnLink.run _ _ _ _ PrimeHonestTranscriptCaller.cipher_code _ _ _ hh hl]
    dsimp only [initial]
    rw [he,pure_bind,hr,BitOracleReturnLink.rename_run _ _ _ PrimeHonestTranscriptCaller.draw_code]
    dsimp only [tail]
    rw [ht]
    simp only [map_bind,map_pure,bind_assoc,pure_bind]
    rfl

#print axioms charged

#print axioms start_entry
end ExplainableCrypto.Helios.Computational.PrimeRequestDraws
