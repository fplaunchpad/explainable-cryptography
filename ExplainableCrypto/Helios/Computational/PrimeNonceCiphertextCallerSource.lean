import ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
/-! Exact joint source law and physical execution for resident caller operands. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- Full caller result at the actual historical source interface. Both sampled
prefixes and the original private context are retained. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (context : List Bool) (rs : ZMod q × ZMod q) : Config :=
  result (primeGroupCoordinate (encryptWith g pk rs.1 (voteScalar vote)).1).val.bits
    (primeGroupCoordinate (encryptWith g pk rs.1 (voteScalar vote)).2).val.bits
    rs.1.val.bits (SamplerOperands.input slack q []) (scalarEncode rs.1) (scalarEncode rs.2)
    (q-1).bits context p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits vote

/-- Proof-side map used only to compare two already executed query trees.
The decoder equation is discharged on their actual encoded pair outputs. -/
private def fromPair (p g pk : Nat) (vote : Bool)
    (cfg : BitOracleMachine.Config 11 PrimeNoncePairMachine.size 3) : Config :=
  let n := ((uniformNatRead (cfg.stk 9)).getD (0,[])).1
  result (g^n%p).bits (((pk^n%p)*(if vote then g else 1))%p).bits
    n.bits (cfg.stk 8) (cfg.stk 9) (cfg.stk 5) (cfg.stk 1) (cfg.stk 10) p.bits g.bits pk.bits vote

private theorem fromPair_result (p g pk n m : Nat) (vote : Bool)
    (record modulus context : List Bool) :
    fromPair p g pk vote (PrimeNoncePairMachine.result record
      (uniformNatEncode n) (uniformNatEncode m) modulus context) =
      result (g^n%p).bits (((pk^n%p)*(if vote then g else 1))%p).bits
        n.bits record (uniformNatEncode n) (uniformNatEncode m) modulus context
        p.bits g.bits pk.bits vote := by
  have h := uniformNatRead_encode n []
  simp only [List.append_nil] at h
  simp [fromPair,PrimeNoncePairMachine.result,h]

private theorem coordinate_bits {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (g pk : PrimeGroup p q) (r : ZMod q) (vote : Bool) (context : List Bool) :
    (((primeGroupCoordinate g).val^r.val%p).bits,
      ((((primeGroupCoordinate pk).val^r.val%p)*(if vote then (primeGroupCoordinate g).val else 1))%p).bits) =
    ((primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).1).val.bits,
      (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).2).val.bits) := by
  have hn := PrimeEncryptMachine.padded_run p (primeGroupCoordinate g).val
    (primeGroupCoordinate pk).val r.val.bits vote context (Fact.out : p.Prime).two_le
    (ZMod.val_lt (primeGroupCoordinate g)) (ZMod.val_lt (primeGroupCoordinate pk))
  have hs := PrimeEncryptMachine.source g pk r vote context
  rw [hn] at hs
  have he := congrArg (fun cfg : PrimeEncryptMachine.Config => (cfg.stk 17,cfg.stk 0)) hs
  simpa [PrimeEncryptMachine.result,bitsValue_bits] using he

private theorem fromPair_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (context : List Bool) (rs : ZMod q × ZMod q) :
    fromPair p (primeGroupCoordinate g).val (primeGroupCoordinate pk).val vote
      (PrimeNoncePairMachine.result (SamplerOperands.input slack q [])
        (scalarEncode rs.1) (scalarEncode rs.2) (q-1).bits context) =
      sourceResult slack g pk vote context rs := by
  change fromPair _ _ _ _ (PrimeNoncePairMachine.result _
    (uniformNatEncode rs.1.val) (uniformNatEncode rs.2.val) _ _) = _
  rw [fromPair_result]
  have h := coordinate_bits g pk rs.1 vote context
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  dsimp only at ha hb
  unfold sourceResult
  rw [ha,hb]
  rfl


/-- Exact joint source tree of the actual caller: two successive nonce draws,
first-nonce routing, and the historical encryptWith computation. -/
theorem execution_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (context : List Bool) :
    Prod.fst <$> BitOracleMachine.run code (clock slack p q)
      (start (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits p.bits
        (SamplerOperands.input slack q []) context vote) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote context <$> runFairBitUniform slack (drawPrimeNoncePair (q := q))) := by
  obtain ⟨c,_,he⟩ := caller_run slack p q (primeGroupCoordinate g).val (primeGroupCoordinate pk).val
    (Fact.out : q.Prime).two_le (Fact.out : p.Prime).two_le
    (ZMod.val_lt (primeGroupCoordinate g)) (ZMod.val_lt (primeGroupCoordinate pk)) context vote
  obtain ⟨d,_,hpair⟩ := PrimeNoncePairMachine.pair_run slack q (Fact.out : q.Prime).two_le context
  have h := congrArg (fun oa => fromPair p (primeGroupCoordinate g).val (primeGroupCoordinate pk).val vote <$> oa)
    (PrimeNoncePairMachine.pair_execution_source (q := q) slack context)
  rw [hpair] at h
  simp only [← simulateQ_map,Functor.map_map,fromPair_source] at h
  rw [he]
  simpa only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,
    fromPair_result,numericResult,nonce] using h

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

/-- The actual caller's branchwise halt and charge establish the compiler
contract, including both samplers, routing, return guard and ciphertext work. -/
theorem within (slack p q g pk limit : Nat) (hq : 2 ≤ q) (hp : 2 ≤ p)
    (hg : g < p) (hpk : pk < p) (context : List Bool) (vote : Bool) :
    BitOracleLoopBounded.Within limit (cost slack p q)
      (BitOracleMachine.run code (clock slack p q)
        (start g.bits pk.bits p.bits (SamplerOperands.input slack q []) context vote)) := by
  obtain ⟨c,hc,he⟩ := caller_run slack p q g pk hq hp hg hpk context vote
  apply within_support
  rw [he]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨a,ha,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨b,hb,ho⟩ := ho
  have hv := eq_of_mem_support_pure _ ho
  subst out
  exact ⟨rfl,hc a (CoinWordLoader.word_length _ _ ha) b (CoinWordLoader.word_length _ _ hb)⟩

/-- Physical execution from the actual resident start and initially empty
auxiliary oracle tapes. Its height includes context and every public/private
input word. Observation is a proof-side readout of the complete caller state. -/
theorem physical_run {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (context : List Bool) :
    let cfg := start (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits p.bits
      (SamplerOperands.input slack q []) context vote
    let B := cost slack p q
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code T
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      (some ∘ sourceResult slack g pk vote context) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (drawPrimeNoncePair (q := q)))) := by
  dsimp only
  have h := BitOraclePrimitiveBounded.run_source_bounded code (clock slack p q) limit (cost slack p q)
    (start (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits p.bits
      (SamplerOperands.input slack q []) context vote) [] (OracleTapeOutput.wordTape [])
    (within slack p q (primeGroupCoordinate g).val (primeGroupCoordinate pk).val limit
      (Fact.out : q.Prime).two_le (Fact.out : p.Prime).two_le
      (ZMod.val_lt (primeGroupCoordinate g)) (ZMod.val_lt (primeGroupCoordinate pk)) context vote)
  simp only [List.length_nil,Nat.add_zero] at h
  rw [h]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (execution_source slack g pk vote context)
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms execution_source
#print axioms within
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.PrimeNonceCiphertextCaller
