import ExplainableCrypto.Helios.Computational.CacheInsertMachine
import ExplainableCrypto.Helios.Computational.CacheReadMachine
import ExplainableCrypto.Helios.Computational.LogAppendMachine

/-! Oracle suspension between executed cache operations. The driver preserves
exact source query syntax. Loading, scalar conversion and transfers remain host
operations; this is not a whole oracle-machine or PPT theorem. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashHandler
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem padded {C : Type} (tick : C → C) (start : C) {u v : Nat}
    (hu : u ≤ v) (hh : tick (tick^[u] start) = tick^[u] start) :
    tick^[v] start = tick^[u] start := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [Nat.add_comm u d,Function.iterate_add_apply]
  exact Function.iterate_fixed hh d

/-- Each canonical field contributes at least its nonempty length header. -/
theorem fields_count_le (ws : List (List Bool)) :
    ws.length ≤ (bitFieldsEncode ws).length := by
  have h : ws.length ≤ (ws.map (fun w => 2*w.length.size+1+w.length)).sum := by
    induction ws with
    | nil => simp
    | cons w ws ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  rw [bitFieldsEncode_length]
  omega

/-- The loaded canonical cache word bounds its actual entry count. -/
theorem entries_le {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    cache.entries.length ≤ ((ballotCacheBitCodec p q).encode cache).length := by
  change cache.entries.length ≤
    (bitFieldsEncode (cache.entries.map (ballotCacheEntryBitCodec p q).encode)).length
  simpa only [List.length_map] using
    fields_count_le (cache.entries.map (ballotCacheEntryBitCodec p q).encode)

/-- Fuel is computed from actual loaded word length, not supplied typed size. -/
def fuel (p q : Nat) (word : List Bool) : Nat :=
  CacheInsertMachine.cost p q word.length word.length

def probe (p q : Nat) (key word : List Bool) : Option (Option (List Bool)) :=
  CacheReadMachine.readout
    (CacheReadMachine.tick^[CacheReadMachine.cost p q word.length word.length]
      (CacheReadMachine.start key word))

def insert (p q : Nat) (key value word : List Bool) : Option (Bool × List Bool) :=
  CacheInsertMachine.readout
    (CacheInsertMachine.tick^[fuel p q word] (CacheInsertMachine.start key value word))

private theorem cost_mono {p q N M W : Nat} (h : N ≤ M) :
    CacheInsertMachine.cost p q N W ≤ CacheInsertMachine.cost p q M W := by
  have hs := Nat.size_le_size h
  have ht := Nat.size_le_size (Nat.add_le_add_right h 1)
  have hi : CacheLookupMachine.iterationCost p q N ≤ CacheLookupMachine.iterationCost p q M := by
    unfold CacheLookupMachine.iterationCost; omega
  have hm := Nat.mul_le_mul h hi
  unfold CacheInsertMachine.cost CacheInsertMachine.builderCost
  omega

/-- Fixed-fuel lookup parses the actual archive and returns canonical scalar digits. -/
theorem probe_encode {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) :
    probe p q ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache) =
      some ((cache.lookup key).map (fun a => a.val.bits)) := by
  obtain ⟨u,hu,hh,ho,_,_⟩ := CacheReadMachine.run cache key
  have hb := hu.trans (CacheReadMachine.cost_mono (entries_le cache) (le_refl _))
  have hf : CacheReadMachine.tick (CacheReadMachine.tick^[u]
      (CacheReadMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache))) =
      CacheReadMachine.tick^[u]
        (CacheReadMachine.start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)) := by
    generalize CacheReadMachine.tick^[u] (CacheReadMachine.start
      ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)) = d at hh ⊢
    rcases d with ⟨l,v,t⟩
    cases hh
    rfl
  unfold probe
  rw [padded _ _ hb hf]
  exact ho

/-- Exact fresh insertion or occupied refusal, with no supplied fuel/freshness. -/
theorem insert_encode {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) :
    insert p q ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
      ((ballotCacheBitCodec p q).encode cache) = some (if cache.lookup key = none
        then (true,(ballotCacheBitCodec p q).encode (cache.insert key value))
        else (false,(ballotCacheBitCodec p q).encode cache)) := by
  obtain ⟨u,hu,hh,ho,_,_⟩ := CacheInsertMachine.run cache key value
  have hb := hu.trans (cost_mono (entries_le cache))
  have hf : CacheInsertMachine.tick (CacheInsertMachine.tick^[u]
      (CacheInsertMachine.start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
        ((ballotCacheBitCodec p q).encode cache))) =
      CacheInsertMachine.tick^[u]
        (CacheInsertMachine.start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
          ((ballotCacheBitCodec p q).encode cache)) := by
    generalize CacheInsertMachine.tick^[u] (CacheInsertMachine.start
      ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
      ((ballotCacheBitCodec p q).encode cache)) = d at hh ⊢
    rcases d with ⟨l,v,t⟩
    cases hh
    rfl
  unfold insert fuel
  rw [padded _ _ hb hf]
  exact ho

variable {p q : Nat} [NeZero p] [NeZero q]
abbrev Log (p q : Nat) := List (Unit × BallotForkPoint (PrimeGroup p q))
abbrev Output (_p q : Nat) := ZMod q × (List Bool × List Bool)

def logEncode (log : Log p q) : List Bool := ((ballotLogEntryBitCodec p q).list).encode log

def append (key word : List Bool) : Option (List Bool) :=
  LogAppendMachine.readout (LogAppendMachine.tick^[LogAppendMachine.cost word.length
    (keyRecordBitBound p) word.length] (LogAppendMachine.start key word))

/-- Actual chronological append, with fuel derived from the loaded log word. -/
theorem append_encode (log : Log p q) (key : BallotForkPoint (PrimeGroup p q)) :
    append (p := p) ((ballotKeyBitCodec p q).encode key) (logEncode log) =
      some (logEncode (log++[((),key)])) := by
  obtain ⟨u,hu,hr⟩ := LogAppendMachine.log_run log key
  have hn : log.length ≤ (logEncode log).length := by
    change log.length ≤ (bitFieldsEncode (log.map (ballotLogEntryBitCodec p q).encode)).length
    simpa only [List.length_map] using fields_count_le (log.map (ballotLogEntryBitCodec p q).encode)
  have hb := hu.trans (LogAppendMachine.cost_mono hn (le_refl _) (le_refl _))
  have hf : LogAppendMachine.tick (LogAppendMachine.tick^[u]
      (LogAppendMachine.start ((ballotKeyBitCodec p q).encode key) (logEncode log))) =
      LogAppendMachine.tick^[u]
        (LogAppendMachine.start ((ballotKeyBitCodec p q).encode key) (logEncode log)) := by
    simp only [logEncode]
    rw [hr]
    rfl
  unfold append logEncode
  simp only [logEncode] at hb hf
  rw [padded _ _ hb hf,hr]
  rfl

def encodeOutput (out : ZMod q × BallotFiniteLoggedState (ZMod q) (PrimeGroup p q)) : Output p q :=
  (out.1,(ballotCacheBitCodec p q).encode out.2.1,logEncode out.2.2)

/-- Prefix writing is executed; obtaining/loading a.val.bits is still a host operation. -/
def scalarWord (a : ZMod q) : Option (List Bool) :=
  FrameWriteMachine.readout (FrameWriteMachine.tick^[3*(q-1).size+3]
    (FrameWriteMachine.state (some .digits) [] [] [] [] a.val.bits none))

theorem scalarWord_encode (a : ZMod q) :
    scalarWord a = some ((primeScalarBitCodec q).encode a) := by
  obtain ⟨u,hu,hr⟩ := FrameWriteMachine.scalar_prefix_run a []
  have hf : FrameWriteMachine.tick (FrameWriteMachine.tick^[u]
      (FrameWriteMachine.state (some .digits) [] [] [] [] a.val.bits none)) =
      FrameWriteMachine.tick^[u] (FrameWriteMachine.state (some .digits) [] [] [] [] a.val.bits none) := by
    rw [hr]; rfl
  unfold scalarWord
  rw [padded _ _ hu hf,hr]
  simp [FrameWriteMachine.readout,FrameWriteMachine.state,primeScalarBitCodec]

/-- Interpretation and range checking at the typed boundary remain host operations. -/
def scalarValue (q : Nat) (digits : List Bool) : Option (ZMod q) :=
  let n := bitsValue digits
  if n < q then some (n : ZMod q) else none

theorem scalarValue_bits (a : ZMod q) : scalarValue q a.val.bits = some a := by
  simp [scalarValue,bitsValue_bits,a.val_lt]

/-- Failure remains explicit. Canonical source inputs never take that branch.
Only a machine-reported miss requests a challenge; insertion runs after it. -/
def hash (key : BallotForkPoint (PrimeGroup p q)) (word log : List Bool) :
    OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) (Option (Output p q)) :=
  match probe p q ((ballotKeyBitCodec p q).encode key) word with
  | none => pure none
  | some (some bits) => pure (scalarValue q bits |>.map fun a => (a,word,log))
  | some none => do
    let a ← FiatShamir.Fork.wrappedChallengeQuery (ZMod q)
    match scalarWord a with
    | none => pure none
    | some bits =>
      match insert p q ((ballotKeyBitCodec p q).encode key) bits word with
      | some (true,next) =>
        match append (p := p) ((ballotKeyBitCodec p q).encode key) log with
        | some log' => pure (some (a,next,log'))
        | none => pure none
      | _ => pure none

private theorem source_hash {F G : Type} [DecidableEq G]
    (key : BallotForkPoint G) (s : BallotFiniteLoggedState F G) :
    (ballotFiniteLoggedImpl (F := F) (G := G) (.inr key)).run s =
      (match s.1.lookup key with
      | some a => pure (a,s)
      | none => do
        let a ← FiatShamir.Fork.wrappedChallengeQuery F
        pure (a,s.1.insert key a,s.2 ++ [((),key)])) := by
  simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run]
  cases s.1.lookup key <;> rfl

/-- Equality in OracleComp preserves the entire request tree, not just its law.
This connects executed cache results to the actual source handler. -/
theorem hash_eq (key : BallotForkPoint (PrimeGroup p q))
    (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q)) :
    hash (p := p) (q := q) key ((ballotCacheBitCodec p q).encode s.1) (logEncode s.2) =
      (fun out => some (encodeOutput out)) <$>
        (ballotFiniteLoggedImpl (F := ZMod q) (G := PrimeGroup p q) (.inr key)).run s := by
  rw [source_hash]
  unfold hash
  rw [probe_encode]
  cases h : s.1.lookup key with
  | some a => simp [scalarValue_bits,encodeOutput]
  | none =>
    simp only [Option.map_none]
    rw [map_bind]
    apply bind_congr
    intro a
    rw [scalarWord_encode]
    dsimp only
    rw [insert_encode]
    simp [h,encodeOutput,append_encode]

/-- A stored challenge returns immediately, with no entropy request. -/
theorem hash_hit (key : BallotForkPoint (PrimeGroup p q))
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (log : Log p q)
    (a : ZMod q) (h : cache.lookup key = some a) :
    hash (p := p) (q := q) key ((ballotCacheBitCodec p q).encode cache) (logEncode log) =
      pure (some (a,(ballotCacheBitCodec p q).encode cache,logEncode log)) := by
  unfold hash
  rw [probe_encode,h]
  simp [scalarValue_bits]

/-- A miss suspends for exactly the original challenge query before insertion. -/
theorem hash_miss (key : BallotForkPoint (PrimeGroup p q))
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) (log : Log p q)
    (h : cache.lookup key = none) :
    hash (p := p) (q := q) key ((ballotCacheBitCodec p q).encode cache) (logEncode log) = (do
      let a ← FiatShamir.Fork.wrappedChallengeQuery (ZMod q)
      pure (some (a,(ballotCacheBitCodec p q).encode (cache.insert key a),logEncode (log ++ [((),key)])))) := by
  unfold hash
  rw [probe_encode,h]
  simp only [Option.map_none]
  apply bind_congr
  intro a
  rw [scalarWord_encode]
  dsimp only
  rw [insert_encode,h]
  simp only [ite_true]
  rw [append_encode]

/-- Execute each source request with the same suspension interface. Continuation
execution and data transfer remain host functions with no machine-cost claim. -/
def run {A : Type} (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) :
    List Bool → List Bool → OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q))
      (Option (A × (List Bool × List Bool))) :=
  OracleComp.construct (fun a word log => pure (some (a,word,log)))
    (fun t _ rec => match t with
      | .inl n => fun word log => do
        let a ← FiatShamir.Fork.wrappedUniformQuery (ZMod q) n
        rec a word log
      | .inr key => fun word log => do
        let result ← hash (p := p) (q := q) key word log
        match result with
        | none => pure none
        | some (a,word',log') => rec a word' log') oa

private theorem source_uniform {F G : Type} [DecidableEq G]
    (n : Nat) (s : BallotFiniteLoggedState F G) :
    (ballotFiniteLoggedImpl (F := F) (G := G) (.inl n)).run s = (do
      let a ← FiatShamir.Fork.wrappedUniformQuery F n
      pure (a,s)) := by
  simp only [ballotFiniteLoggedImpl,QueryImpl.add,StateT.run]

attribute [local irreducible] hash probe insert append scalarWord

/-- Every source program preserves its exact request tree, output, ordered
cache and miss log under machine-backed hash handling. No caller correspondence. -/
theorem run_eq {A : Type} (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A)
    (s : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q)) :
    run (p := p) (q := q) oa ((ballotCacheBitCodec p q).encode s.1) (logEncode s.2) =
      (fun out => some (out.1,(ballotCacheBitCodec p q).encode out.2.1,logEncode out.2.2)) <$>
        runBallotFiniteLogged (F := ZMod q) (G := PrimeGroup p q) oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    rw [show run (p := p) (q := q) (pure a) ((ballotCacheBitCodec p q).encode s.1) (logEncode s.2) =
      pure (some (a,(ballotCacheBitCodec p q).encode s.1,logEncode s.2)) from rfl]
    simp [runBallotFiniteLogged]
  | query_bind t next ih =>
    unfold runBallotFiniteLogged
    rw [run_simulateQ_query_bind,map_bind]
    cases t with
    | inl n =>
      rw [source_uniform,bind_assoc]
      change (FiatShamir.Fork.wrappedUniformQuery (ZMod q) n >>= fun a =>
        run (p := p) (q := q) (next a) ((ballotCacheBitCodec p q).encode s.1) (logEncode s.2)) = _
      apply bind_congr
      intro a
      simpa only [pure_bind,runBallotFiniteLogged] using ih a s
    | inr key =>
      have hr : run (p := p) (q := q)
          (liftM ((BallotOracleSpec (ZMod q) (PrimeGroup p q)).query (.inr key)) >>= next)
          ((ballotCacheBitCodec p q).encode s.1) (logEncode s.2) =
          (hash (p := p) (q := q) key ((ballotCacheBitCodec p q).encode s.1) (logEncode s.2) >>= fun result =>
            match result with
            | none => pure none
            | some (a,w,l) => run (p := p) (q := q) (next a) w l) := by rfl
      rw [hr,hash_eq,bind_map_left]
      apply bind_congr
      intro result
      simpa only [encodeOutput,runBallotFiniteLogged] using ih result.1 result.2

open BallotCacheCodecControls in
/-- Literal late hit: answer three, old cache and pre-existing log, no query. -/
theorem hit_control :
    hash key ((ballotCacheBitCodec 23 11).encode cache) (logEncode [((),otherKey)]) =
      pure (some (3,(ballotCacheBitCodec 23 11).encode cache,logEncode [((),otherKey)])) := by
  exact hash_hit key cache _ 3 (by decide)

open BallotCacheCodecControls in
/-- Empty cache with nonempty old log: sample, singleton cache, append at tail. -/
theorem miss_control :
    hash key ((ballotCacheBitCodec 23 11).encode ∅) (logEncode [((),otherKey)]) = (do
      let a ← FiatShamir.Fork.wrappedChallengeQuery (ZMod 11)
      pure (some (a,(ballotCacheBitCodec 23 11).encode (AList.singleton key a),
        logEncode [((),otherKey),((),key)]))) := by
  rw [hash_miss key ∅ _ (by rfl)]
  apply bind_congr
  intro a
  rfl

open BallotCacheCodecControls in
/-- The literal hit cannot be an eager-resampling handler, for any continuation. -/
theorem hit_not_resampled
    (next : ZMod 11 → OracleComp (FiatShamir.Fork.wrappedSpec (ZMod 11))
      (Option (Output 23 11))) :
    hash key ((ballotCacheBitCodec 23 11).encode cache) (logEncode [((),otherKey)]) ≠
      (FiatShamir.Fork.wrappedChallengeQuery (ZMod 11) >>= next) := by
  rw [hit_control]
  intro h
  have hp := congrArg OracleComp.isPure h
  simp only [FiatShamir.Fork.wrappedChallengeQuery,OracleComp.isPure_query_bind,
    OracleComp.isPure_pure,Bool.true_eq_false] at hp

open BallotCacheCodecControls in
/-- The literal miss cannot return immediately, even with a fabricated result. -/
theorem miss_not_immediate (out : Option (Output 23 11)) :
    hash key ((ballotCacheBitCodec 23 11).encode ∅) (logEncode [((),otherKey)]) ≠ pure out := by
  rw [miss_control]
  intro h
  have hp := congrArg OracleComp.isPure h
  simp only [FiatShamir.Fork.wrappedChallengeQuery,OracleComp.isPure_query_bind,
    OracleComp.isPure_pure,Bool.false_eq_true] at hp

#print axioms scalarValue_bits
#print axioms scalarWord_encode
#print axioms append_encode
#print axioms probe_encode
#print axioms insert_encode
#print axioms hash_eq
#print axioms hash_hit
#print axioms hash_miss
#print axioms run_eq
#print axioms hit_control
#print axioms miss_control
#print axioms hit_not_resampled
#print axioms miss_not_immediate
end ExplainableCrypto.Helios.Computational.CacheHashHandler
