import ExplainableCrypto.Helios.Computational.CacheRoutineCode

namespace ExplainableCrypto.Helios.Computational.CacheInsertMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- Exact occupied state from actual canonical source words, with retained proposed answer. -/
theorem occupied_full_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value old : ZMod q)
    (h : cache.lookup key = some old) :
    ∃ fuel ≤ 2*((ballotCacheBitCodec p q).encode cache).length + 3*cache.entries.length.size +
      cache.entries.length*CacheLookupMachine.iterationCost p q cache.entries.length + 9,
      ∃ n tail,
        tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
          ((ballotCacheBitCodec p q).encode cache)) =
        state none ((ballotKeyBitCodec p q).encode key) tail [] [] [] (n+1).bits
          ((primeScalarBitCodec q).encode old) ((ballotCacheBitCodec p q).encode cache)
          ((primeScalarBitCodec q).encode value) (some false) := by
  obtain ⟨j,hj,n,tail,hr⟩ := CacheLookupMachine.hit_run cache key old h
  let initial := CacheLookupMachine.start ((ballotKeyBitCodec p q).encode key)
    ((ballotCacheBitCodec p q).encode cache)
  let frame : Unit → List Bool := fun _ => (primeScalarBitCodec q).encode value
  have hc := TM2StackFrame.run (Equiv.refl (CacheLookupMachine.Stack ⊕ Unit))
    CacheLookupMachine.program j initial frame
  change (TM2ReturnLink.tick (fun l => TM2StackFrame.relocate (Equiv.refl _) (CacheLookupMachine.program l)))^[j] _ =
    TM2StackFrame.embed (Equiv.refl _) (CacheLookupMachine.tick^[j] initial) frame at hc
  dsimp only [initial] at hc
  rw [hr] at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run
    (fun l => TM2StackFrame.relocate (Equiv.refl _) (CacheLookupMachine.program l))
    program Label.lookup Label.lookupDone (fun _ => rfl) j
    (TM2StackFrame.embed (Equiv.refl _) initial frame) (by dsimp only [initial]; rw [hc]; rfl)
  dsimp only [initial] at he
  rw [hc] at he
  have ho : TM2ReturnLink.embed Label.lookup Label.lookupDone
      (TM2StackFrame.embed (Equiv.refl _)
        (CacheLookupMachine.state none ((ballotKeyBitCodec p q).encode key) tail [] [] [] (n+1).bits
          ((primeScalarBitCodec q).encode old) ((ballotCacheBitCodec p q).encode cache) (some true)) frame) =
      state (some .lookupDone) ((ballotKeyBitCodec p q).encode key) tail [] [] [] (n+1).bits
        ((primeScalarBitCodec q).encode old) ((ballotCacheBitCodec p q).encode cache)
        ((primeScalarBitCodec q).encode value) (some true) := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    rcases k with (k|u)
    · rfl
    · cases u; rfl
  rw [ho] at he
  change tick^[u] _ = _ at he
  refine ⟨u+1,by omega,n,tail,?_⟩
  change tick^[u+1] (TM2ReturnLink.embed Label.lookup Label.lookupDone
    (TM2StackFrame.embed (Equiv.refl _) (CacheLookupMachine.start _ _) frame)) = _
  rw [Function.iterate_succ_apply',he]
  rfl

/-- The existing finite insertion adapter preserves the full occupied result and
arbitrary three-port frame, with the actual charge bounded by the used fuel. -/
theorem occupied_charged_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value old : ZMod q)
    (h : cache.lookup key = some old) (frame : Fin 3 → List Bool) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      ∃ charge ≤ 32*fuel, ∃ n tail,
        BitOracleMachine.run (fun l => .compute (CacheRoutineCode.insertCode l)) fuel
          (CacheRoutineCode.insertState (start ((ballotKeyBitCodec p q).encode key)
            ((primeScalarBitCodec q).encode value) ((ballotCacheBitCodec p q).encode cache)) frame) =
        pure (CacheRoutineCode.insertState
          (state none ((ballotKeyBitCodec p q).encode key) tail [] [] [] (n+1).bits
            ((primeScalarBitCodec q).encode old) ((ballotCacheBitCodec p q).encode cache)
            ((primeScalarBitCodec q).encode value) (some false)) frame,charge) := by
  obtain ⟨fuel,hf,n,tail,hr⟩ := occupied_full_run cache key value old h
  obtain ⟨charge,hc,he⟩ := CacheRoutineCode.insert_run fuel
    (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
      ((ballotCacheBitCodec p q).encode cache)) frame
  rw [hr] at he
  exact ⟨fuel,by unfold cost; omega,charge,hc,n,tail,he⟩

/-- Even a singleton occupied cache cannot have blank work after insertion;
the actual lookup leaves a positive counter and the insertion branch retains it. -/
theorem occupied_counter_not_empty {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value old : ZMod q)
    (h : cache.lookup key = some old) :
    ∃ fuel ≤ cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length,
      let cfg := tick^[fuel] (start ((ballotKeyBitCodec p q).encode key) ((primeScalarBitCodec q).encode value)
        ((ballotCacheBitCodec p q).encode cache))
      cfg.l = none ∧ cfg.var = some false ∧ cfg.stk outer ≠ [] := by
  obtain ⟨fuel,hf,n,tail,he⟩ := occupied_full_run cache key value old h
  refine ⟨fuel,by unfold cost; omega,?_⟩
  dsimp only
  rw [he]
  refine ⟨rfl,rfl,?_⟩
  change (n+1).bits ≠ []
  intro hzero
  have hs : (n+1).size = 0 := by rw [←Nat.size_eq_bits_len,hzero]; rfl
  have := Nat.size_eq_zero.mp hs
  omega

#print axioms occupied_full_run
#print axioms occupied_charged_run
#print axioms occupied_counter_not_empty
end ExplainableCrypto.Helios.Computational.CacheInsertMachine
