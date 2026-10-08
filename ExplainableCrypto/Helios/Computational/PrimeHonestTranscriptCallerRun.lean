import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
import ExplainableCrypto.Helios.Computational.PrimeTranscriptDrawsRun
import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachineSource

/-! Derived reachable input origins, live composition and complete charge bound. -/
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
open OracleComp OracleSpec BitOracleMachine
/-- The linked caller starts with the original raw input on port seven and
blank work. The entry label executes the existing input copier. -/
theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7
      (some (cipherLabel (PrimeHonestCiphertextMachine.inputLabel
        (PrimeHonestInputMachine.copyLabel 0)))) 0 raw := rfl

/-- No prepared caller words are added to the physical startup height. -/
theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length := by
  change TM2TapeRuns.height (PrimeHonestCiphertextMachine.start raw).stk = raw.length
  exact PrimeHonestCiphertextMachine.start_height raw

/-- Proof-side extraction of the next entry from an actual reached ciphertext
configuration. The result bridge below proves all retained port identities. -/
def continuation (cfg : PrimeHonestCiphertextMachine.Config) (vote : Bool) : PrimeTranscriptDraws.Config :=
  PrimeTranscriptDraws.start (cfg.stk 17) (cfg.stk 0) (cfg.stk 13) (cfg.stk 19)
    (cfg.stk 20) (cfg.stk 21) (cfg.stk 22) (cfg.stk 14) (cfg.stk 6)
    (cfg.stk 16) (cfg.stk 15) vote

theorem continuation_result
    (alpha beta nonce record first second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    continuation (PrimeHonestCiphertextMachine.result alpha beta nonce record first second samplerMod context modulus g pk vote) vote =
    PrimeTranscriptDraws.start alpha beta nonce record first second samplerMod context modulus g pk vote := rfl

#print axioms start_source
#print axioms start_height
#print axioms continuation_result
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller

namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
open OracleComp OracleSpec BitOracleMachine
/-- Reachable numeric output of the already checked raw-input prefix. -/
def prefixResult (slack p q g pk : Nat) (context : List Bool) (vote : Bool)
    (a b : List Bool) : PrimeHonestCiphertextMachine.Config :=
  BitOracleReturnLink.embed PrimeHonestCiphertextMachine.callerLabel none
    (PrimeNonceCiphertextCaller.numericResult slack p q g pk context vote a b)

theorem prefix_return (slack p q g pk : Nat) (context : List Bool) (vote : Bool) (a b : List Bool) :
    BitOracleReturnLink.embed cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
      (prefixResult slack p q g pk context vote a b) =
    BitOracleReturnLink.embed drawLabel none (continuation (prefixResult slack p q g pk context vote a b) vote) := rfl

#print axioms prefix_return
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem tail_bound (slack p q g pk : Nat) (hq : 0 < q)
    (context : List Bool) (vote : Bool) (a b : List Bool) :
    ∀ out ∈ support (BitOracleMachine.run PrimeTranscriptDraws.code (PrimeTranscriptDraws.clock slack q)
      (continuation (prefixResult slack p q g pk context vote a b) vote)),
      out.1.l = none ∧ out.2 ≤ PrimeTranscriptDraws.cost slack q := by
  obtain ⟨charge,hc,he⟩ := PrimeTranscriptDraws.charged slack q hq
    (g^PrimeNonceCiphertextCaller.nonce q a%p).bits
    (((pk^PrimeNonceCiphertextCaller.nonce q a%p)*(if vote then g else 1))%p).bits
    (PrimeNonceCiphertextCaller.nonce q a).bits
    (uniformNatEncode (PrimeNonceCiphertextCaller.nonce q a))
    (uniformNatEncode (PrimeNonceCiphertextCaller.nonce q b))
    (q-1).bits context p.bits g.bits pk.bits vote
  change ∀ out ∈ support (BitOracleMachine.run PrimeTranscriptDraws.code (PrimeTranscriptDraws.clock slack q)
    (PrimeTranscriptDraws.start (g^PrimeNonceCiphertextCaller.nonce q a%p).bits
      (((pk^PrimeNonceCiphertextCaller.nonce q a%p)*(if vote then g else 1))%p).bits
      (PrimeNonceCiphertextCaller.nonce q a).bits (SamplerOperands.input slack q [])
      (uniformNatEncode (PrimeNonceCiphertextCaller.nonce q a))
      (uniformNatEncode (PrimeNonceCiphertextCaller.nonce q b))
      (q-1).bits context p.bits g.bits pk.bits vote)), _
  rw [he]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨c,hc',ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨e,he',ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨z0,hz0,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨z1,hz1,ho⟩ := ho
  have hv := eq_of_mem_support_pure _ ho
  subst out
  exact ⟨rfl,hc c (CoinWordLoader.word_length _ _ hc') e (CoinWordLoader.word_length _ _ he')
    z0 (CoinWordLoader.word_length _ _ hz0) z1 (CoinWordLoader.word_length _ _ hz1)⟩

/-- One uninterrupted execution links the actual raw initializer/ciphertext
run to all four simulator draws, preserving both complete query trees and the
sum of their actual charges. All return-state premises are derived. -/
theorem linked_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (slack : Nat) (vote : Bool) (saved : List Bool) :
    let raw := PrimeHonestInputMachine.input g pk slack vote saved
    BitOracleMachine.run code (clock raw slack p q) (start raw) = (do
      let first ← BitOracleMachine.run PrimeHonestCiphertextMachine.code
        (PrimeHonestCiphertextMachine.clock raw slack p q) (PrimeHonestCiphertextMachine.start raw)
      let last ← BitOracleMachine.run PrimeTranscriptDraws.code (PrimeTranscriptDraws.clock slack q)
        (continuation first.1 vote)
      pure (BitOracleReturnLink.embed drawLabel none last.1,first.2+last.2)) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote saved
  obtain ⟨charge,hc,he⟩ := PrimeHonestCiphertextMachine.charged g pk slack vote saved
  have hh : ∀ out ∈ support (BitOracleMachine.run PrimeHonestCiphertextMachine.code
      (PrimeHonestCiphertextMachine.clock raw slack p q) (PrimeHonestCiphertextMachine.start raw)),
      out.1.l = none := by
    rw [he]
    intro out ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨a,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨b,_,ho⟩ := ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rfl
  have ht : ∀ out ∈ support (BitOracleMachine.run PrimeHonestCiphertextMachine.code
      (PrimeHonestCiphertextMachine.clock raw slack p q) (PrimeHonestCiphertextMachine.start raw)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeTranscriptDraws.clock slack q)
        (BitOracleReturnLink.embed cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0))) out.1)),
      last.1.l = none := by
    rw [he]
    intro out ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨a,_,ho⟩ := ho
    rw [mem_support_bind_iff] at ho
    obtain ⟨b,_,ho⟩ := ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeTranscriptDraws.clock slack q)
      (BitOracleReturnLink.embed cipherLabel (some (drawLabel (PrimeTranscriptDraws.sampleLabel 0 0)))
        (prefixResult slack p q (primeGroupCoordinate g).val (primeGroupCoordinate pk).val raw vote a b))), _
    rw [prefix_return,BitOracleReturnLink.rename_run _ _ _ draw_code]
    intro last hl
    obtain ⟨v,hv,rfl⟩ := mem_support_map_peel _ _ hl
    have hv' := (tail_bound slack p q (primeGroupCoordinate g).val (primeGroupCoordinate pk).val
      (Fact.out : q.Prime).pos raw vote a b v hv).1
    change v.1.l.elim none (some ∘ drawLabel) = none
    rw [hv']
    rfl
  change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed cipherLabel _ _) = _
  rw [BitOracleReturnLink.run _ _ _ _ cipher_code _ _ _ hh ht]
  apply bind_congr_of_forall_mem_support
  intro first hf
  rw [he] at hf
  rw [mem_support_bind_iff] at hf
  obtain ⟨a,_,hf⟩ := hf
  rw [mem_support_bind_iff] at hf
  obtain ⟨b,_,hf⟩ := hf
  have hv := eq_of_mem_support_pure _ hf
  subst first
  change (do
    let last ← BitOracleMachine.run code (PrimeTranscriptDraws.clock slack q)
      (BitOracleReturnLink.embed cipherLabel _ (prefixResult slack p q _ _ raw vote a b))
    pure (last.1,charge a b+last.2)) = _
  rw [prefix_return,BitOracleReturnLink.rename_run _ _ _ draw_code]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  rfl

#print axioms linked_run
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem within_support (limit bound : Nat) (oa : OracleComp spec (Config × Nat))
    (h : ∀ out ∈ support oa, out.1.l = none ∧ out.2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound oa := by
  induction oa using OracleComp.inductionOn with
  | pure out => exact h out (by simp)
  | query_bind t next ih =>
    intro answer _
    apply ih answer
    intro out ho
    exact h out (by
      rw [mem_support_bind_iff]
      exact ⟨answer,by simp only [support_liftM]; exact ⟨answer,rfl⟩,ho⟩)

/-- Every supported leaf of the actual raw prefix halts within the derived
sum of constituent charges. This is the same support argument used by Within,
exposed for the next uninterrupted caller's cost composition. -/
theorem run_support {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    ∀ out ∈ support (BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote saved))),
      out.1.l = none ∧ out.2 ≤ cost (PrimeHonestInputMachine.input g pk slack vote saved) slack p q := by
  obtain ⟨charge,hc,he⟩ := PrimeHonestCiphertextMachine.charged g pk slack vote saved
  rw [linked_run,he]
  simp only [bind_assoc,pure_bind]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨a,ha,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨b,hb,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨last,hl,ho⟩ := ho
  have hv := eq_of_mem_support_pure _ ho
  subst out
  have hp := hc a (CoinWordLoader.word_length _ _ ha) b (CoinWordLoader.word_length _ _ hb)
  have ht := tail_bound slack p q (primeGroupCoordinate g).val (primeGroupCoordinate pk).val
    (Fact.out : q.Prime).pos (PrimeHonestInputMachine.input g pk slack vote saved) vote a b last hl
  constructor
  · change last.1.l.elim none (some ∘ drawLabel) = none
    rw [ht.1]
    rfl
  · change charge a b + last.2 ≤ _
    unfold cost
    omega

/-- The raw initializer, two nonce draws, first ciphertext and four simulator
draws all halt within their derived sum of actual execution charges. -/
theorem within {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    BitOracleLoopBounded.Within limit
      (cost (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (BitOracleMachine.run code
        (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
        (start (PrimeHonestInputMachine.input g pk slack vote saved))) := by
  exact within_support limit _ _ (run_support slack g pk vote saved)

#print axioms run_support
#print axioms within
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
