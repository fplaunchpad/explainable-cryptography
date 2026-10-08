import ExplainableCrypto.Helios.Computational.CacheHashHandler
import ExplainableCrypto.Helios.Computational.CacheHashMachine

/-! Word-facing cache requests using executed coin sampling on misses.
The driver still loads operands and composes routines through host control;
whole-caller compilation and its physical runtime bound remain separate. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashCoins
open OracleComp OracleSpec
abbrev Output := List Bool × (List Bool × List Bool)

/-- Only the coin branch is reached by the scalar program, as `sample_eq` derives. -/
private def coins : QueryImpl BitOracleMachine.spec (OracleComp coinSpec) := fun r =>
  match r with
  | .coin => coin
  | .hash word => pure word

private theorem coins_lift {A : Type} (oa : OracleComp coinSpec A) :
    simulateQ coins (simulateQ CoinWordLoader.liftCoins oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
    cases t
    simp [simulateQ_bind,CoinWordLoader.liftCoins,ih]
    rfl

def sample (q : Nat) (width : List Bool) : OracleComp coinSpec (List Bool) :=
  simulateQ coins ((fun out => out.1.stk 5) <$>
    BitOracleMachine.run CoinScalarMachine.code (CoinScalarMachine.clock width.length q)
      (CoinScalarMachine.start width q))

/-- Exact encoded query-tree observation of the executed sampler. -/
theorem sample_eq (q : Nat) [NeZero q] (width : List Bool) :
    sample q width = (fun a => uniformNatEncode a.val) <$> sampleFairBitModulo q width.length := by
  rw [sample,CoinScalarMachine.sampler_value,coins_lift]

/-- Prepare the modulus and width from one serialized input, then sample.
Constructing/loading that input record remains part of the enclosing caller. -/
def prepared (mode : Bool) (slack n : Nat) : OracleComp coinSpec (List Bool) :=
  simulateQ coins ((fun out => out.1.stk 5) <$>
    BitOracleMachine.run PreparedScalarMachine.code (PreparedScalarMachine.clock mode slack n)
      (PreparedScalarMachine.startWord mode (SamplerOperands.input slack n [])))

theorem prepared_eq (mode : Bool) (slack n : Nat) [NeZero (SamplerOperands.range mode n)] :
    prepared mode slack n = (fun a => uniformNatEncode a.val) <$>
      sampleFairBitRange (SamplerOperands.range mode n) slack := by
  rw [prepared,PreparedScalarMachine.sampler_value,coins_lift]

/-- The actual miss sampler copies its operand record from caller storage while
retaining the request, cache and log in the common twelve-port workspace. -/
def preparedHash (slack q : Nat) (key cache log : List Bool) : OracleComp coinSpec (List Bool) :=
  simulateQ coins ((fun out => out.1.stk 5) <$>
    BitOracleMachine.run CacheHashMachine.sampleCode (CacheHashMachine.sampleClock slack q)
      (CacheHashMachine.sampleStart (SamplerOperands.input slack q []) key cache log))

theorem preparedHash_eq (slack q : Nat) [NeZero q] (key cache log : List Bool) :
    preparedHash slack q key cache log =
      (fun a => uniformNatEncode a.val) <$> sampleFairBitRange q slack := by
  rw [preparedHash,CacheHashMachine.sample_value,coins_lift]

/-- A cache hit supplies already parsed digits directly to the existing writer. -/
def writeDigits (q : Nat) (digits : List Bool) : Option (List Bool) :=
  FrameWriteMachine.readout (FrameWriteMachine.tick^[3*(q-1).size+3]
    (FrameWriteMachine.state (some .digits) [] [] [] [] digits none))

theorem writeDigits_encode {q : Nat} [NeZero q] (a : ZMod q) :
    writeDigits q a.val.bits = some ((primeScalarBitCodec q).encode a) :=
  CacheHashHandler.scalarWord_encode a

/-- Insert the sampler's actual encoded word, then append the original key to the log. -/
def finish (p q : Nat) (key value word log : List Bool) : Option Output :=
  match CacheHashHandler.insert p q key value word with
  | some (true,next) => (CacheHashHandler.append (p := p) key log).map fun log' => (value,next,log')
  | _ => none

/-- The raw key, cache and log are loaded words. A malformed probe returns failure;
hits do not sample, and misses pass the produced word directly to insertion. -/
def hash (p q : Nat) (width key word log : List Bool) : OracleComp coinSpec (Option Output) :=
  match CacheHashHandler.probe p q key word with
  | none => pure none
  | some (some digits) => pure ((writeDigits q digits).map fun value => (value,word,log))
  | some none => do
    let value ← sample q width
    pure (finish p q key value word log)

/-- The current cache miss executes serialized operand preparation as well as
sampling. The original arbitrary-width handler remains a checked reference. -/
def hashPrepared (p q : Nat) [NeZero q] (slack : Nat) (key word log : List Bool) :
    OracleComp coinSpec (Option Output) :=
  match CacheHashHandler.probe p q key word with
  | none => pure none
  | some (some digits) => pure ((writeDigits q digits).map fun value => (value,word,log))
  | some none => do
    let value ← preparedHash slack q key word log
    pure (finish p q key value word log)

/-- Preparation changes no complete cache-request query tree or observation. -/
theorem hashPrepared_eq (p q : Nat) [NeZero q] (slack : Nat) (key word log : List Bool) :
    hashPrepared p q slack key word log =
      hash p q (List.replicate (q.size+slack) true) key word log := by
  simp only [hashPrepared,hash,preparedHash_eq,sample_eq,List.length_replicate,
    sampleFairBitRange]

variable {p q : Nat} [NeZero p] [NeZero q]
abbrev State (p q : Nat) := BallotFiniteLoggedState (ZMod q) (PrimeGroup p q)

def encode (out : ZMod q × State p q) : Output :=
  ((primeScalarBitCodec q).encode out.1,(ballotCacheBitCodec p q).encode out.2.1,
    CacheHashHandler.logEncode out.2.2)

private theorem finish_encode (key : BallotForkPoint (PrimeGroup p q)) (a : ZMod q)
    (state : State p q) (hh : state.1.lookup key = none) :
    finish p q ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode a)
      ((ballotCacheBitCodec p q).encode state.1) (CacheHashHandler.logEncode state.2) =
        some (encode (a,state.1.insert key a,state.2++[((),key)])) := by
  simp [finish,CacheHashHandler.insert_encode,hh,CacheHashHandler.append_encode,encode]

/-- Hits return the stored scalar encoding with unchanged cache/log and no coin query. -/
theorem hash_hit (width : List Bool) (key : BallotForkPoint (PrimeGroup p q))
    (state : State p q) (a : ZMod q) (hh : state.1.lookup key = some a) :
    hash p q width ((ballotKeyBitCodec p q).encode key)
      ((ballotCacheBitCodec p q).encode state.1) (CacheHashHandler.logEncode state.2) =
        pure (some (encode (a,state))) := by
  simp [hash,CacheHashHandler.probe_encode,hh,writeDigits_encode,encode]

private theorem scalar_fin (a : Fin q) :
    uniformNatEncode a.val = (primeScalarBitCodec q).encode ((ZMod.finEquiv q) a) := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

/-- Misses run the actual sampler, and preserve the complete new cache and ordered log. -/
theorem hash_miss (width : List Bool) (key : BallotForkPoint (PrimeGroup p q))
    (state : State p q) (hh : state.1.lookup key = none) :
    hash p q width ((ballotKeyBitCodec p q).encode key)
      ((ballotCacheBitCodec p q).encode state.1) (CacheHashHandler.logEncode state.2) =
        (fun a : Fin q => some (encode ((ZMod.finEquiv q) a,
          state.1.insert key ((ZMod.finEquiv q) a),state.2++[((),key)]))) <$>
            sampleFairBitModulo q width.length := by
  simp only [hash,CacheHashHandler.probe_encode,hh,Option.map_none,sample_eq]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  apply bind_congr
  intro a
  rw [scalar_fin,finish_encode key _ state hh]

/-- Reference source with the original exact-uniform challenge distribution. -/
def ideal (key : BallotForkPoint (PrimeGroup p q)) (state : State p q) : ProbComp (Option Output) :=
  match state.1.lookup key with
  | some a => pure (some (encode (a,state)))
  | none => (fun a : Fin q => some (encode ((ZMod.finEquiv q) a,
      state.1.insert key ((ZMod.finEquiv q) a),state.2++[((),key)]))) <$> uniformSample (Fin q)

/-- Canonical exact-uniform interpretation of the original wrapped source. -/
def exactChallenge : QueryImpl (FiatShamir.Fork.wrappedSpec (ZMod q)) ProbComp := fun t =>
  match t with
  | .inl n => liftM (unifSpec.query n)
  | .inr _ => (ZMod.finEquiv q) <$> uniformSample (Fin q)

/-- This is the pinned library's actual canonical scalar sampler. -/
theorem exactChallenge_value : exactChallenge (q := q) (.inr ()) = uniformSample (ZMod q) := by
  rfl

/-- The comparison distribution is the actual original finite logged source,
with the entire response, cache and miss log encoded. -/
theorem hash_source (key : BallotForkPoint (PrimeGroup p q)) (state : State p q) :
    ideal key state = (fun out => some (encode out)) <$>
      simulateQ exactChallenge
        ((ballotFiniteLoggedImpl (F := ZMod q) (G := PrimeGroup p q) (.inr key)).run state) := by
  have he : ((ballotFiniteLoggedImpl (F := ZMod q) (G := PrimeGroup p q) (.inr key)).run state) =
      (match state.1.lookup key with
      | some a => pure (a,state)
      | none => do
        let a ← FiatShamir.Fork.wrappedChallengeQuery (ZMod q)
        pure (a,state.1.insert key a,state.2++[((),key)])) := by
    simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run]
    cases state.1.lookup key <;> rfl
  rw [he]
  cases hh : state.1.lookup key with
  | some a => simp [ideal,hh]
  | none =>
    simp [ideal,hh,FiatShamir.Fork.wrappedChallengeQuery,exactChallenge,Functor.map_map]

/-- Complete answer/cache/log variation distance; this is a one-request bound,
including hits, and does not assert exact uniformity for arbitrary q. -/
theorem hash_distance (slack : Nat) (key : BallotForkPoint (PrimeGroup p q)) (state : State p q) :
    SPMF.tvDist
      (evalSPMF (hash p q (List.replicate (q.size+slack) true)
        ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode state.1)
        (CacheHashHandler.logEncode state.2)))
      (evalSPMF ((fun out => some (encode out)) <$>
        simulateQ exactChallenge
          ((ballotFiniteLoggedImpl (F := ZMod q) (G := PrimeGroup p q) (.inr key)).run state)))
      ≤ ((2 : ℝ)^slack)⁻¹ := by
  rw [← hash_source]
  cases hh : state.1.lookup key with
  | some a => rw [hash_hit _ key state a hh]; simp [ideal,hh]
  | none =>
    rw [hash_miss _ key state hh]
    simp only [List.length_replicate,ideal,hh,evalSPMF_map]
    exact (SPMF.tvDist_map_le _ _ _).trans (sampleFairBitRange_tv_le q slack)

end ExplainableCrypto.Helios.Computational.CacheHashCoins
