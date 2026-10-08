import ExplainableCrypto.Helios.Computational.CacheHashDispatch

/-! Composition of the actual cache dispatcher. Every intermediate workspace and
return flag below is derived from the original routine's complete post-state. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashDispatch
open Turing.TM2 OracleComp BitOracleMachine CacheRoutineCode
set_option maxRecDepth 8192

private theorem sequence_run (a b c : Config 12 size 3) (f g x y : Nat)
    (hf : run code f a = pure (b,x)) (hg : run code g b = pure (c,y)) :
    run code (f+g) a = pure (c,x+y) := by
  rw [BitOracleReturnLink.run_add,hf,pure_bind,hg,pure_bind]

private theorem link_run {l : Nat} (p : Code 12 l 3) (labels : Fin l → Fin size) (ret : Fin size)
    (hp : ∀ label, code (labels label) = BitOracleReturnLink.command labels (some ret) (p label))
    (a b : Config 12 l 3) (c : Config 12 size 3) (f g x y : Nat)
    (hf : run p f a = pure (b,x)) (hb : b.l = none)
    (hg : run code g (BitOracleReturnLink.embed labels (some ret) b) = pure (c,y))
    (hc : c.l = none) :
    run code (f+g) (BitOracleReturnLink.embed labels (some ret) a) = pure (c,x+y) := by
  have hh : ∀ out ∈ support (run p f a), out.1.l = none := by
    rw [hf]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out; exact hb
  have ht : ∀ out ∈ support (run p f a),
      ∀ last ∈ support (run code g (BitOracleReturnLink.embed labels (some ret) out.1)),
        last.1.l = none := by
    rw [hf]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out
    rw [hg]; intro last hl
    have he := eq_of_mem_support_pure _ hl
    subst last; exact hc
  rw [BitOracleReturnLink.run p code labels ret hp f g a hh ht,hf,pure_bind,hg,pure_bind]

private theorem one_run (a b : Config 12 size 3) (x : Nat)
    (hs : BitOracleMachine.step code a = pure (b,x)) : run code 1 a = pure (b,x) := by
  simp [run,hs]

/-- Final log cleanup executes on the real controller and preserves all retained
words. No empty log or private-record premise is needed. -/
theorem finish_log (key cache log record value : List Bool) (memory : Fin 3) :
    run code (log.length+1)
      ⟨some 11,memory,![[],[],[],[],[],[],log,value,key,cache,log,record]⟩ =
      pure (result key cache log record value,4*(log.length+1)) := by
  have he := clear_run 6 11 success rfl log (result key cache log record value).stk memory
  have hi : (⟨some 11,memory,Function.update (result key cache log record value).stk 6 log⟩ : Config 12 size 3) =
      ⟨some 11,memory,![[],[],[],[],[],[],log,value,key,cache,log,record]⟩ := by
    congr 1; funext k; fin_cases k <;> rfl
  have ho : stepAux success 0 (Function.update (result key cache log record value).stk 6 []) =
      result key cache log record value := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hi,ho] at he
  simpa [clear,success,localCost,Nat.mul_comm] using he

/-- Copy the new chronological log into its retained port and clear the consumed
work output. The original copy program supplies the restoration and charge. -/
theorem finish_copy (key cache log record value : List Bool) :
    ∃ charge ≤ 32*((2*log.length+2)+(log.length+1)),
      run code ((2*log.length+2)+(log.length+1))
        ⟨some (copyLabel 2 0),0,![[],[],[],[],[],[],log,value,key,cache,[],record]⟩ =
        pure (result key cache log record value,charge) := by
  let frame : Fin 9 → List Bool := ![[],[],[],[],[],value,key,cache,record]
  obtain ⟨charge,hc,hr⟩ := copy_run 2 log [] frame
  have ht : run code (log.length+1)
      (BitOracleReturnLink.embed (copyLabel 2) (some 11)
        (copyState 2 (BitCopyMachine.config none log (log++[]) []) frame)) =
      pure (result key cache log record value,4*(log.length+1)) := by
    have he : BitOracleReturnLink.embed (copyLabel 2) (some 11)
        (copyState 2 (BitCopyMachine.config none log (log++[]) []) frame) =
        (⟨some 11,0,![[],[],[],[],[],[],log,value,key,cache,log,record]⟩ : Config 12 size 3) := by
      simp only [List.append_nil]
      change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    rw [he]; exact finish_log key cache log record value 0
  have he := link_run _ (copyLabel 2) 11 (copy_code 2) _ _ _ _ _ _ _ hr rfl ht rfl
  refine ⟨charge+4*(log.length+1),by omega,?_⟩
  have hi : BitOracleReturnLink.embed (copyLabel 2) (some 11)
      (copyState 2 (BitCopyMachine.config (some false) log [] []) frame) =
      (⟨some (copyLabel 2 0),0,![[],[],[],[],[],[],log,value,key,cache,[],record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rwa [hi] at he


/-- Executed append, transfer and cleanup following successful insertion. The
cache, scalar and private record are arbitrary preserved words. -/
theorem append_tail {p q : Nat} [NeZero p] [NeZero q]
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (cache record value : List Bool) :
    ∃ fuel ≤ 1 + LogAppendMachine.cost log.length (keyRecordBitBound p)
        (((ballotLogEntryBitCodec p q).list).encode log).length + 1 +
        (3*(((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])).length+3),
      ∃ charge ≤ 32*fuel,
      run code fuel ⟨some 9,2,![[],[],[],[],[],[],[],value,
        (ballotKeyBitCodec p q).encode key,cache,((ballotLogEntryBitCodec p q).list).encode log,record]⟩ =
      pure (result ((ballotKeyBitCodec p q).encode key) cache
        (((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])) record value,charge) := by
  let K := (ballotKeyBitCodec p q).encode key
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let L' := ((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])
  let frame : Fin 4 → List Bool := ![[],value,cache,record]
  obtain ⟨last,hl,ht⟩ := finish_copy K cache L' record value
  have gate : run code 1
      ⟨some 10,2,![[],[],[],[],[],[],L',value,K,cache,[],record]⟩ =
      pure (⟨some (copyLabel 2 0),0,![[],[],[],[],[],[],L',value,K,cache,[],record]⟩,3) :=
    one_run _ _ _ rfl
  have hg := sequence_run _ _ _ _ _ _ _ gate ht
  obtain ⟨f,hf,hr⟩ := LogAppendMachine.log_run log key
  obtain ⟨charge,hc,he⟩ := CacheRoutineCode.append_run f (LogAppendMachine.start K L) frame
  rw [hr] at he
  have hi : BitOracleReturnLink.embed appendLabel (some 10)
      (appendState (LogAppendMachine.start K L) frame) =
      (⟨some (appendLabel (appendLabels default)),0,![[],[],[],[],[],[],[],value,K,cache,L,record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : BitOracleReturnLink.embed appendLabel (some 10)
      (appendState (LogAppendMachine.state none [] [] [] L' [] [] K [] (some true)) frame) =
      (⟨some 10,2,![[],[],[],[],[],[],L',value,K,cache,[],record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [← ho] at hg
  have linked := link_run _ appendLabel 10 append_code _ _ _ _ _ _ _ he rfl hg rfl
  rw [hi] at linked
  have entry : run code 1
      ⟨some 9,2,![[],[],[],[],[],[],[],value,K,cache,L,record]⟩ =
      pure (⟨some (appendLabel (appendLabels default)),0,![[],[],[],[],[],[],[],value,K,cache,L,record]⟩,3) :=
    one_run _ _ _ rfl
  have whole := sequence_run _ _ _ _ _ _ _ entry linked
  refine ⟨1+(f+(1+((2*L'.length+2)+(L'.length+1)))),by dsimp only [L'] at *; omega,
    3+(charge+(3+last)),by omega,whole⟩


/-- Input-derived bound for the actual append and final transfer. -/
def appendClock {p q : Nat} [NeZero p] [NeZero q]
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) : Nat :=
  1 + LogAppendMachine.cost log.length (keyRecordBitBound p)
    (((ballotLogEntryBitCodec p q).list).encode log).length + 1 +
    (3*(((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])).length+3)

/-- A miss derived by the probe is the freshness premise of guarded insertion.
Its full post-state establishes the subsequent append workspace. -/
theorem insert_tail {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (record : List Bool)
    (fresh : cache.lookup key = none) :
    ∃ fuel ≤ CacheInsertMachine.cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length +
        appendClock key log,
      ∃ charge ≤ 32*fuel,
      run code fuel ⟨some (insertLabel (insertLabels default)),0,
        ![(ballotCacheBitCodec p q).encode cache,[],[],[],[],[],[],(primeScalarBitCodec q).encode value,
          (ballotKeyBitCodec p q).encode key,[],((ballotLogEntryBitCodec p q).list).encode log,record]⟩ =
      pure (result ((ballotKeyBitCodec p q).encode key)
        ((ballotCacheBitCodec p q).encode (cache.insert key value))
        (((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])) record
        ((primeScalarBitCodec q).encode value),charge) := by
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  let C' := (ballotCacheBitCodec p q).encode (cache.insert key value)
  let V := (primeScalarBitCodec q).encode value
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let frame : Fin 3 → List Bool := ![[],L,record]
  obtain ⟨g,hg,last,hl,ht⟩ := append_tail key log C' record V
  obtain ⟨f,hf,hr⟩ := CacheInsertMachine.fresh_run cache key value fresh
  obtain ⟨charge,hc,he⟩ := CacheRoutineCode.insert_run f (CacheInsertMachine.start K V C) frame
  rw [hr] at he
  have hi : BitOracleReturnLink.embed insertLabel (some 9)
      (insertState (CacheInsertMachine.start K V C) frame) =
      (⟨some (insertLabel (insertLabels default)),0,![C,[],[],[],[],[],[],V,K,[],L,record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ho : BitOracleReturnLink.embed insertLabel (some 9)
      (insertState (CacheInsertMachine.state none K [] [] [] [] [] [] C' V (some true)) frame) =
      (⟨some 9,2,![[],[],[],[],[],[],[],V,K,C',L,record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [← ho] at ht
  have whole := link_run _ insertLabel 9 insert_code _ _ _ _ _ _ _ he rfl ht rfl
  rw [hi] at whole
  exact ⟨f+g,Nat.add_le_add hf hg,charge+last,by omega,whole⟩

/-- Controller cleanup followed by a halting continuation. This is a local
composition lemma for the actual code, with the code equality discharged at use. -/
private theorem clear_then (port : Fin 12) (again next : Fin size)
    (hcode : code again = .compute (clear port again (enter next)))
    (word : List Bool) (words : Fin 12 → List Bool) (memory : Fin 3)
    (fuel charge : Nat) (done : Config 12 size 3)
    (ht : run code fuel ⟨some next,0,Function.update words port []⟩ = pure (done,charge)) :
    run code (word.length+1+fuel)
      ⟨some again,memory,Function.update words port word⟩ =
      pure (done,4*(word.length+1)+charge) := by
  have he := clear_run port again (enter next) hcode word words memory
  have he' : run code (word.length+1) ⟨some again,memory,Function.update words port word⟩ =
      pure (⟨some next,0,Function.update words port []⟩,4*(word.length+1)) := by
    simpa [enter,stepAux,clear,localCost,Nat.mul_comm] using he
  exact sequence_run _ _ _ _ _ _ _ he' ht

/-- Copy the retained original cache into insertion's destructive input and clear
its archive port before invoking the already proved insertion/append tail. -/
theorem cache_transfer_tail {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (record : List Bool)
    (fresh : cache.lookup key = none) :
    ∃ fuel ≤ 3*((ballotCacheBitCodec p q).encode cache).length+3+
        CacheInsertMachine.cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length +
        appendClock key log,
      ∃ charge ≤ 32*fuel,
      run code fuel ⟨some (copyLabel 1 0),0,
        ![[],[],[],[],[],[],[],(primeScalarBitCodec q).encode value,
          (ballotKeyBitCodec p q).encode key,(ballotCacheBitCodec p q).encode cache,
          ((ballotLogEntryBitCodec p q).list).encode log,record]⟩ =
      pure (result ((ballotKeyBitCodec p q).encode key)
        ((ballotCacheBitCodec p q).encode (cache.insert key value))
        (((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])) record
        ((primeScalarBitCodec q).encode value),charge) := by
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  let V := (primeScalarBitCodec q).encode value
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let W : Fin 12 → List Bool := ![C,[],[],[],[],[],[],V,K,[],L,record]
  let frame : Fin 9 → List Bool := ![[],[],[],[],[],V,K,L,record]
  obtain ⟨g,hg,last,hl,ht⟩ := insert_tail cache key value log record fresh
  have wu : Function.update W 9 [] = W := by funext k; fin_cases k <;> rfl
  have ht' := ht
  change run code g ⟨some (insertLabel (insertLabels default)),0,W⟩ = _ at ht'
  rw [← wu] at ht'
  have cleared := clear_then 9 8 (insertLabel (insertLabels default)) rfl C W 0 g last _ ht'
  obtain ⟨charge,hc,he⟩ := copy_run 1 C [] frame
  have ho : BitOracleReturnLink.embed (copyLabel 1) (some 8)
      (copyState 1 (BitCopyMachine.config none C (C++[]) []) frame) =
      (⟨some 8,0,Function.update W 9 C⟩ : Config 12 size 3) := by
    simp only [List.append_nil]
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [← ho] at cleared
  have whole := link_run _ (copyLabel 1) 8 (copy_code 1) _ _ _ _ _ _ _ he rfl cleared rfl
  have hi : BitOracleReturnLink.embed (copyLabel 1) (some 8)
      (copyState 1 (BitCopyMachine.config (some false) C [] []) frame) =
      (⟨some (copyLabel 1 0),0,![[],[],[],[],[],[],[],V,K,C,L,record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hi] at whole
  refine ⟨(2*C.length+2)+(C.length+1+g),by dsimp only [C] at *; omega,
    charge+(4*(C.length+1)+last),by omega,whole⟩


/-- A common bound for the deterministic tail after any sampled scalar. It
uses the modulus width, not a supplied branch runtime certificate. -/
def missTailClock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) : Nat :=
  3*(2*(q-1).size+1)+q.size+5+3*((ballotCacheBitCodec p q).encode cache).length+3+
    CacheInsertMachine.cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length +
    appendClock key log

/-- The actual successful sampler return drives answer transfer, modulus and
scratch cleanup, original-cache transfer, insertion and chronological append. -/
theorem miss_tail {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (record : List Bool)
    (fresh : cache.lookup key = none) :
    ∃ fuel ≤ missTailClock cache key log, ∃ charge ≤ 32*fuel,
      run code fuel ⟨some 5,2,![[],q.bits,[],[],[],(primeScalarBitCodec q).encode value,[],[],
        (ballotKeyBitCodec p q).encode key,(ballotCacheBitCodec p q).encode cache,
        ((ballotLogEntryBitCodec p q).list).encode log,record]⟩ =
      pure (result ((ballotKeyBitCodec p q).encode key)
        ((ballotCacheBitCodec p q).encode (cache.insert key value))
        (((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])) record
        ((primeScalarBitCodec q).encode value),charge) := by
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  let V := (primeScalarBitCodec q).encode value
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let W : Fin 12 → List Bool := ![[],[],[],[],[],[],[],V,K,C,L,record]
  let Q : Fin 12 → List Bool := ![[],q.bits,[],[],[],[],[],V,K,C,L,record]
  let frame : Fin 9 → List Bool := ![q.bits,[],[],[],[],K,C,L,record]
  obtain ⟨g,hg,last,hl,ht⟩ := cache_transfer_tail cache key value log record fresh
  have wu : Function.update W 1 [] = W := by funext k; fin_cases k <;> rfl
  change run code g ⟨some (copyLabel 1 0),0,W⟩ = _ at ht
  rw [← wu] at ht
  have clearQ := clear_then 1 7 (copyLabel 1 0) rfl q.bits W 0 g last _ ht
  have wq : Function.update W 1 q.bits = Q := by funext k; fin_cases k <;> rfl
  rw [wq] at clearQ
  have qu : Function.update Q 5 [] = Q := by funext k; fin_cases k <;> rfl
  rw [← qu] at clearQ
  have clearV := clear_then 5 6 7 rfl V Q 0 _ _ _ clearQ
  obtain ⟨charge,hc,he⟩ := copy_run 0 V [] frame
  have ho : BitOracleReturnLink.embed (copyLabel 0) (some 6)
      (copyState 0 (BitCopyMachine.config none V (V++[]) []) frame) =
      (⟨some 6,0,Function.update Q 5 V⟩ : Config 12 size 3) := by
    simp only [List.append_nil]
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [← ho] at clearV
  have linked := link_run _ (copyLabel 0) 6 (copy_code 0) _ _ _ _ _ _ _ he rfl clearV rfl
  have hi : BitOracleReturnLink.embed (copyLabel 0) (some 6)
      (copyState 0 (BitCopyMachine.config (some false) V [] []) frame) =
      (⟨some (copyLabel 0 0),0,![[],q.bits,[],[],[],V,[],[],K,C,L,record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hi] at linked
  have gate : run code 1 ⟨some 5,2,![[],q.bits,[],[],[],V,[],[],K,C,L,record]⟩ =
      pure (⟨some (copyLabel 0 0),0,![[],q.bits,[],[],[],V,[],[],K,C,L,record]⟩,3) :=
    one_run _ _ _ rfl
  have whole := sequence_run _ _ _ _ _ _ _ gate linked
  have hv : V.length ≤ 2*(q-1).size+1 := scalarEncode_length_le value
  have hq : q.bits.length = q.size := by rw [← Nat.size_eq_bits_len]
  refine ⟨1+((2*V.length+2)+(V.length+1+(q.bits.length+1+g))),?_,
    3+(charge+(4*(V.length+1)+(4*(q.bits.length+1)+last))),by omega,whole⟩
  unfold missTailClock
  omega

/-- Pad only the final halt, giving every possible scalar one common tail clock. -/
theorem miss_tail_fixed {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (record : List Bool)
    (fresh : cache.lookup key = none) :
    ∃ charge ≤ 32*missTailClock cache key log,
      run code (missTailClock cache key log)
        ⟨some 5,2,![[],q.bits,[],[],[],(primeScalarBitCodec q).encode value,[],[],
          (ballotKeyBitCodec p q).encode key,(ballotCacheBitCodec p q).encode cache,
          ((ballotLogEntryBitCodec p q).list).encode log,record]⟩ =
      pure (result ((ballotKeyBitCodec p q).encode key)
        ((ballotCacheBitCodec p q).encode (cache.insert key value))
        (((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])) record
        ((primeScalarBitCodec q).encode value),charge) := by
  obtain ⟨fuel,hf,charge,hc,he⟩ := miss_tail cache key value log record fresh
  have hh : ∀ out ∈ support (run code fuel
      ⟨some 5,2,![[],q.bits,[],[],[],(primeScalarBitCodec q).encode value,[],[],
        (ballotKeyBitCodec p q).encode key,(ballotCacheBitCodec p q).encode cache,
        ((ballotLogEntryBitCodec p q).list).encode log,record]⟩), out.1.l = none := by
    rw [he]; intro out ho
    have h := eq_of_mem_support_pure _ ho
    subst out; rfl
  have hp := BitOracleReturnLink.padded code fuel (missTailClock cache key log-fuel) _ hh
  rw [Nat.sub_add_cancel hf,he] at hp
  exact ⟨charge,hc.trans (Nat.mul_le_mul_left _ hf),hp⟩


/-- Full specification result for the scalar determined by a chronological coin
word. It includes all work ports and the retained local operand record. -/
def sampledResult {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (record bits : List Bool) : Config 12 size 3 :=
  result ((ballotKeyBitCodec p q).encode key)
    ((ballotCacheBitCodec p q).encode (cache.insert key (bitsValue bits : ZMod q)))
    (((ballotLogEntryBitCodec p q).list).encode (log++[((),key)])) record
    ((primeScalarBitCodec q).encode (bitsValue bits : ZMod q))

/-- The actual sampler and its entire miss continuation form one raw coin-query
tree, with an input-derived combined clock and charge. Freshness is supplied by
the enclosing probe, rather than assumed by insertion's implementation. -/
theorem sampled_tail {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat)
    (fresh : cache.lookup key = none) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = q.size+slack →
        charge bits ≤ CacheHashMachine.sampleCost slack q+32*missTailClock cache key log) ∧
      run code (CacheHashMachine.sampleClock slack q+missTailClock cache key log)
        ⟨some (sampleLabel 0),0,![[],[],[],[],[],[],[],[],
          (ballotKeyBitCodec p q).encode key,(ballotCacheBitCodec p q).encode cache,
          ((ballotLogEntryBitCodec p q).list).encode log,SamplerOperands.input slack q []]⟩ =
      (fun bits => (sampledResult cache key log (SamplerOperands.input slack q []) bits,charge bits)) <$>
        CoinWordLoader.word (q.size+slack) := by
  classical
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let R := SamplerOperands.input slack q []
  obtain ⟨first,hf,hr⟩ := CacheHashMachine.sample_run slack q (Nat.pos_of_ne_zero (NeZero.ne _)) K C L
  choose last hl ht using fun bits : List Bool =>
    miss_tail_fixed cache key (bitsValue bits : ZMod q) log R fresh
  have tail (bits : List Bool) :
      run code (missTailClock cache key log)
        (BitOracleReturnLink.embed sampleLabel (some 5)
          (CacheHashMachine.sampleResult (uniformNatEncode (bitsValue bits % q)) q.bits K C L R)) =
      pure (sampledResult cache key log R bits,last bits) := by
    have hv : uniformNatEncode (bitsValue bits % q) =
        (primeScalarBitCodec q).encode (bitsValue bits : ZMod q) := by
      simp [primeScalarBitCodec,scalarEncode,ZMod.val_natCast]
    have he : BitOracleReturnLink.embed sampleLabel (some 5)
        (CacheHashMachine.sampleResult (uniformNatEncode (bitsValue bits % q)) q.bits K C L R) =
        (⟨some 5,2,![[],q.bits,[],[],[],(primeScalarBitCodec q).encode (bitsValue bits : ZMod q),[],[],K,C,L,R]⟩ : Config 12 size 3) := by
      rw [hv]
      change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    rw [he]; exact ht bits
  have hh : ∀ out ∈ support (run CacheHashMachine.sampleCode (CacheHashMachine.sampleClock slack q)
      (CacheHashMachine.sampleStart R K C L)), out.1.l = none := by
    rw [hr]; intro out ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rfl
  have hc : ∀ out ∈ support (run CacheHashMachine.sampleCode (CacheHashMachine.sampleClock slack q)
      (CacheHashMachine.sampleStart R K C L)),
      ∀ done ∈ support (run code (missTailClock cache key log)
        (BitOracleReturnLink.embed sampleLabel (some 5) out.1)), done.1.l = none := by
    rw [hr]; intro out ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    rw [tail]; intro done hd
    have he := eq_of_mem_support_pure _ hd
    subst done; rfl
  have whole := BitOracleReturnLink.run CacheHashMachine.sampleCode code sampleLabel 5 sample_code
    (CacheHashMachine.sampleClock slack q) (missTailClock cache key log)
    (CacheHashMachine.sampleStart R K C L) hh hc
  have hi : BitOracleReturnLink.embed sampleLabel (some 5) (CacheHashMachine.sampleStart R K C L) =
      (⟨some (sampleLabel 0),0,![[],[],[],[],[],[],[],[],K,C,L,R]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hi,hr] at whole
  refine ⟨fun bits => first bits+last bits,fun bits hb => Nat.add_le_add (hf bits hb) (hl bits),?_⟩
  rw [whole]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_apply]
  apply bind_congr
  intro bits
  rw [tail bits]
  rfl


/-- Hits execute both residual-work cleanups and the original scalar writer.
No assumption that the probe counter or unread suffix is empty is made. -/
theorem hit_tail {q : Nat} [NeZero q] (key cache log record : List Bool)
    (value : ZMod q) (counter tail : List Bool) :
    ∃ fuel ≤ tail.length+1+(3*(q-1).size+3)+(counter.length+1), ∃ charge ≤ 32*fuel,
      run code fuel ⟨some 2,0,![tail,[],[],value.val.bits,counter,[],[],[],key,cache,log,record]⟩ =
      pure (result key cache log record ((primeScalarBitCodec q).encode value),charge) := by
  let V := (primeScalarBitCodec q).encode value
  let W : Fin 12 → List Bool := ![[],[],[],[],[],[],[],V,key,cache,log,record]
  let frame : Fin 7 → List Bool := ![counter,[],[],key,cache,log,record]
  have cleared := clear_run 4 3 success rfl counter W 2
  have ci : (⟨some 3,2,Function.update W 4 counter⟩ : Config 12 size 3) =
      ⟨some 3,2,![[],[],[],[],counter,[],[],V,key,cache,log,record]⟩ := by
    congr 1; funext k; fin_cases k <;> rfl
  have co : stepAux success 0 (Function.update W 4 []) = result key cache log record V := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [ci,co] at cleared
  have cleared' : run code (counter.length+1)
      ⟨some 3,2,![[],[],[],[],counter,[],[],V,key,cache,log,record]⟩ =
      pure (result key cache log record V,4*(counter.length+1)) := by
    simpa [clear,success,localCost,Nat.mul_comm] using cleared
  obtain ⟨f,hf,hr⟩ := FrameWriteMachine.scalar_prefix_run value []
  obtain ⟨charge,hc,he⟩ := CacheRoutineCode.writer_run f
    (FrameWriteMachine.state (some .digits) [] [] [] [] value.val.bits none) frame
  rw [hr] at he
  simp only [List.append_nil] at he
  have ho : BitOracleReturnLink.embed writerLabel (some 3)
      (writerState (FrameWriteMachine.state none [] [] [] V [] (some true)) frame) =
      (⟨some 3,2,![[],[],[],[],counter,[],[],V,key,cache,log,record]⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [← ho] at cleared'
  have linked := link_run _ writerLabel 3 writer_code _ _ _ _ _ _ _ he rfl cleared' rfl
  let D : Fin 12 → List Bool := ![[],[],[],value.val.bits,counter,[],[],[],key,cache,log,record]
  have hi : BitOracleReturnLink.embed writerLabel (some 3)
      (writerState (FrameWriteMachine.state (some .digits) [] [] [] [] value.val.bits none) frame) =
      (⟨some (writerLabel (writerLabels .digits)),0,D⟩ : Config 12 size 3) := by
    change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  rw [hi] at linked
  have du : Function.update D 0 [] = D := by funext k; fin_cases k <;> rfl
  rw [← du] at linked
  have whole := clear_then 0 2 (writerLabel (writerLabels .digits)) rfl tail D 0 _ _ _ linked
  have di : (⟨some 2,0,Function.update D 0 tail⟩ : Config 12 size 3) =
      ⟨some 2,0,![tail,[],[],value.val.bits,counter,[],[],[],key,cache,log,record]⟩ := by
    congr 1; funext k; fin_cases k <;> rfl
  rw [di] at whole
  exact ⟨tail.length+1+(f+(counter.length+1)),by omega,
    4*(tail.length+1)+(charge+4*(counter.length+1)),by omega,whole⟩


/-- Probe clock from actual input sizes. -/
def probeClock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) : Nat :=
  CacheReadMachine.cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length

def missClock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : Nat :=
  1+probeClock cache+(2+(CacheHashMachine.sampleClock slack q+missTailClock cache key log))

def missCost {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : Nat :=
  2+32*probeClock cache+(6+(CacheHashMachine.sampleCost slack q+32*missTailClock cache key log))

/-- Complete actual request on a cache miss: the probe derives the sampler's
workspace and insertion freshness; no intermediate-state or cost premise remains.
The conclusion preserves the complete raw coin tree and final caller storage. -/
theorem miss_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat)
    (fresh : cache.lookup key = none) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = q.size+slack → charge bits ≤ missCost cache key log slack) ∧
      run code (missClock cache key log slack)
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
          (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q [])) =
      (fun bits => (sampledResult cache key log (SamplerOperands.input slack q []) bits,charge bits)) <$>
        CoinWordLoader.word (q.size+slack) := by
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let R := SamplerOperands.input slack q []
  obtain ⟨last,hl,ht⟩ := sampled_tail cache key log slack fresh
  have gate1 : run code 1
      ⟨some 1,1,![[],[],[],[],[],[],[],[],K,C,L,R]⟩ =
      pure (⟨some 4,0,![[],[],[],[],[],[],[],[],K,C,L,R]⟩,4) := one_run _ _ _ rfl
  have gate4 : run code 1
      ⟨some 4,0,![[],[],[],[],[],[],[],[],K,C,L,R]⟩ =
      pure (⟨some (sampleLabel 0),0,![[],[],[],[],[],[],[],[],K,C,L,R]⟩,2) := one_run _ _ _ rfl
  have gates := sequence_run _ _ _ _ _ _ _ gate1 gate4
  change run code 2 (BitOracleReturnLink.embed readLabel (some 1) (probeMiss K C L R)) =
    pure (⟨some (sampleLabel 0),0,![[],[],[],[],[],[],[],[],K,C,L,R]⟩,6) at gates
  have tail : run code (2+(CacheHashMachine.sampleClock slack q+missTailClock cache key log))
      (BitOracleReturnLink.embed readLabel (some 1) (probeMiss K C L R)) =
      (fun bits => (sampledResult cache key log R bits,6+last bits)) <$> CoinWordLoader.word (q.size+slack) := by
    rw [BitOracleReturnLink.run_add,gates,pure_bind,ht]
    simp [map_eq_bind_pure_comp,bind_assoc,R]
  obtain ⟨f,hf,first,hfirst,hr⟩ := probe_miss cache key L R fresh
  change f ≤ probeClock cache at hf
  have hh : ∀ out ∈ support (run (fun label => .compute (readCode label)) f (probeStart K C L R)),
      out.1.l = none := by
    rw [hr]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out; rfl
  have hp := BitOracleReturnLink.padded (fun label => .compute (readCode label)) f
    (probeClock cache-f) (probeStart K C L R) hh
  rw [Nat.sub_add_cancel hf,hr] at hp
  have hh' : ∀ out ∈ support (run (fun label => .compute (readCode label))
      (probeClock cache) (probeStart K C L R)), out.1.l = none := by
    rw [hp]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out; rfl
  have hc : ∀ out ∈ support (run (fun label => .compute (readCode label))
      (probeClock cache) (probeStart K C L R)),
      ∀ done ∈ support (run code (2+(CacheHashMachine.sampleClock slack q+missTailClock cache key log))
        (BitOracleReturnLink.embed readLabel (some 1) out.1)), done.1.l = none := by
    rw [hp]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out
    rw [tail]; intro done hd
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ hd
    rfl
  have linked := BitOracleReturnLink.run (fun label => .compute (readCode label)) code readLabel 1 read_code
    (probeClock cache) (2+(CacheHashMachine.sampleClock slack q+missTailClock cache key log))
    (probeStart K C L R) hh' hc
  rw [hp,pure_bind,tail] at linked
  have entry : run code 1 (start K C L R) =
      pure (BitOracleReturnLink.embed readLabel (some 1) (probeStart K C L R),2) := one_run _ _ _ rfl
  refine ⟨fun bits => 2+(first+(6+last bits)),?_,?_⟩
  · intro bits hb
    have h := hl bits hb
    dsimp only
    unfold missCost
    have hfirst' := hfirst.trans (Nat.mul_le_mul_left 32 hf)
    change first ≤ 32*probeClock cache at hfirst'
    omega
  · unfold missClock
    rw [show 1+probeClock cache+(2+(CacheHashMachine.sampleClock slack q+missTailClock cache key log)) =
      1+(probeClock cache+(2+(CacheHashMachine.sampleClock slack q+missTailClock cache key log))) by omega]
    rw [BitOracleReturnLink.run_add,entry,pure_bind,linked]
    simp [map_eq_bind_pure_comp,bind_assoc,R]


/-- Existing deterministic stack-growth bound, instantiated at the actual probe.
The code-access factor is a fixed constant independent of election parameters. -/
def probeSpace {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (log record : List Bool) : Nat :=
  TM2TapeRuns.height (probeStart ((ballotKeyBitCodec p q).encode key)
    ((ballotCacheBitCodec p q).encode cache) log record).stk +
    probeClock cache * TM2TapeRuns.codeAccesses readCode

def hitTailClock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (log record : List Bool) : Nat :=
  2*(probeSpace cache key log record+1)+(3*(q-1).size+3)

def hitClock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (log record : List Bool) : Nat :=
  1+(probeClock cache+(1+hitTailClock cache key log record))

def hitCost {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (log record : List Bool) : Nat :=
  2+(32*probeClock cache+(4+32*hitTailClock cache key log record))

/-- Complete actual hit request, without a supplied workspace/growth certificate.
The probe derives its scalar and residual scratch; the existing deterministic
machine growth theorem bounds that scratch. Hits make no oracle query. -/
theorem hit_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) (log record : List Bool)
    (found : cache.lookup key = some value) :
    ∃ charge ≤ hitCost cache key log record,
      run code (hitClock cache key log record)
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache) log record) =
      pure (result ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
        log record ((primeScalarBitCodec q).encode value),charge) := by
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  obtain ⟨f,hf,first,hfirst,n,tail,hr⟩ := probe_hit cache key value log record found
  change f ≤ probeClock cache at hf
  have projected := BitOracleMachine.local_run readCode f (probeStart K C log record)
  rw [hr,map_pure] at projected
  have source_eq := ((pure_inj _ _).mp projected).symm
  obtain ⟨used,hu,physical,growth⟩ := TM2TapeRuns.run_packed readCode f (probeStart K C log record)
  rw [source_eq] at growth
  have hm := Nat.mul_le_mul_right (TM2TapeRuns.codeAccesses readCode) hf
  have tailBound : tail.length ≤ probeSpace cache key log record :=
    (growth 0).trans (Nat.add_le_add_left hm _)
  have counterBound : (n+1).bits.length ≤ probeSpace cache key log record :=
    (growth 4).trans (Nat.add_le_add_left hm _)
  obtain ⟨g,hg,last,hl,ht⟩ := hit_tail K C log record value (n+1).bits tail
  have hg' : g ≤ hitTailClock cache key log record := by unfold hitTailClock; omega
  have hhTail : ∀ out ∈ support (run code g
      ⟨some 2,0,![tail,[],[],value.val.bits,(n+1).bits,[],[],[],K,C,log,record]⟩), out.1.l = none := by
    rw [ht]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out; rfl
  have paddedTail := BitOracleReturnLink.padded code g (hitTailClock cache key log record-g) _ hhTail
  rw [Nat.sub_add_cancel hg',ht] at paddedTail
  have gate : run code 1
      (BitOracleReturnLink.embed readLabel (some 1) (probeHit K C log record value.val.bits (n+1).bits tail)) =
      pure (⟨some 2,0,![tail,[],[],value.val.bits,(n+1).bits,[],[],[],K,C,log,record]⟩,4) :=
    one_run _ _ _ rfl
  have continuation := sequence_run _ _ _ _ _ _ _ gate paddedTail
  have hh : ∀ out ∈ support (run (fun label => .compute (readCode label)) f (probeStart K C log record)),
      out.1.l = none := by
    rw [hr]; intro out ho
    have he := eq_of_mem_support_pure _ ho
    subst out; rfl
  have hp := BitOracleReturnLink.padded (fun label => .compute (readCode label)) f
    (probeClock cache-f) (probeStart K C log record) hh
  rw [Nat.sub_add_cancel hf,hr] at hp
  have linked := link_run _ readLabel 1 read_code _ _ _ _ _ _ _ hp rfl continuation rfl
  have entry : run code 1 (start K C log record) =
      pure (BitOracleReturnLink.embed readLabel (some 1) (probeStart K C log record),2) := one_run _ _ _ rfl
  have whole := sequence_run _ _ _ _ _ _ _ entry linked
  refine ⟨2+(first+(4+last)),?_,whole⟩
  have hfirst' := hfirst.trans (Nat.mul_le_mul_left 32 hf)
  have hlast := hl.trans (Nat.mul_le_mul_left 32 hg')
  unfold hitCost
  omega


/-- Complete source-level request specification, including private retained data.
Hits preserve cache/log; misses append only the newly sampled key. -/
def request {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : OracleComp spec (Config 12 size 3) :=
  match cache.lookup key with
  | some value => pure (result ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
      (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q [])
      ((primeScalarBitCodec q).encode value))
  | none => sampledResult cache key log (SamplerOperands.input slack q []) <$>
      CoinWordLoader.word (q.size+slack)

def requestClock {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : Nat :=
  max (missClock cache key log slack)
    (hitClock cache key (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))

def requestCost {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) : Nat :=
  max (missCost cache key log slack)
    (hitCost cache key (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))

/-- Every typed finite cache/key/log runs in one fixed dispatcher, with complete
query-tree/state correspondence, derived halt and derived charge on every leaf.
No lookup outcome, intermediate workspace, freshness or cost premise is supplied. -/
theorem request_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    let execution := run code (requestClock cache key log slack)
      (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
        (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))
    (Prod.fst <$> execution = request cache key log slack) ∧
      ∀ out ∈ support execution, out.1.l = none ∧ out.2 ≤ requestCost cache key log slack := by
  dsimp only
  cases found : cache.lookup key with
  | none =>
    obtain ⟨charge,hc,he⟩ := miss_run cache key log slack found
    have hf : missClock cache key log slack ≤ requestClock cache key log slack := Nat.le_max_left _ _
    have hh : ∀ out ∈ support (run code (missClock cache key log slack)
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
          (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))), out.1.l = none := by
      rw [he]; intro out ho
      obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
      rfl
    have hp := BitOracleReturnLink.padded code (missClock cache key log slack)
      (requestClock cache key log slack-missClock cache key log slack) _ hh
    rw [Nat.sub_add_cancel hf,he] at hp
    rw [hp]
    refine ⟨by simp [request,found,Functor.map_map],?_⟩
    intro out ho
    obtain ⟨bits,hb,rfl⟩ := mem_support_map_peel _ _ ho
    exact ⟨rfl,(hc bits (CoinWordLoader.word_length _ _ hb)).trans (Nat.le_max_left _ _)⟩
  | some value =>
    obtain ⟨charge,hc,he⟩ := hit_run cache key value
      (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []) found
    have hf : hitClock cache key (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []) ≤
        requestClock cache key log slack := Nat.le_max_right _ _
    have hh : ∀ out ∈ support (run code
        (hitClock cache key (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
          (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))), out.1.l = none := by
      rw [he]; intro out ho
      have h := eq_of_mem_support_pure _ ho
      subst out; rfl
    have hp := BitOracleReturnLink.padded code _
      (requestClock cache key log slack-hitClock cache key
        (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q [])) _ hh
    rw [Nat.sub_add_cancel hf,he] at hp
    rw [hp]
    refine ⟨by simp [request,found],?_⟩
    intro out ho
    have h := eq_of_mem_support_pure _ ho
    subst out
    exact ⟨rfl,hc.trans (Nat.le_max_right _ _)⟩

attribute [local irreducible] code requestClock requestCost

private theorem within_support (limit bound : Nat)
    (oa : OracleComp spec (Config 12 size 3 × Nat))
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

/-- Discharge the existing physical compiler's termination/charge contract from
the actual full request, for any bounded-oracle policy. -/
theorem within {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack limit : Nat) :
    BitOracleLoopBounded.Within limit (requestCost cache key log slack)
      (run code (requestClock cache key log slack)
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
          (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))) :=
  within_support limit _ _ (request_run cache key log slack).2

/-- The existing primitive compiler executes the whole request from the common
loaded caller layout with its derived clock. Loading the surrounding caller's
serialized input and invoking its next continuation remain enclosing work. -/
theorem physical_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack limit : Nat) :
    let cfg := start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
      (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q [])
    let B := requestCost cache key log slack
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code T
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      some <$> simulateQ (BitOracleLoopBounded.adapter limit) (request cache key log slack) := by
  dsimp only
  have he := BitOraclePrimitiveBounded.run_source_bounded code (requestClock cache key log slack) limit
    (requestCost cache key log slack)
    (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
      (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []))
    [] (OracleTapeOutput.wordTape []) (within cache key log slack limit)
  simp only [List.length_nil,Nat.add_zero] at he
  rw [he]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (request_run cache key log slack).1
  simp only [simulateQ_map] at hr
  rw [← hr,Functor.map_map]

end ExplainableCrypto.Helios.Computational.CacheHashDispatch
