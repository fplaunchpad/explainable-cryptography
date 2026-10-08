import ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachine
namespace ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachine
open Turing.TM2 BitOracleMachine OracleComp
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
attribute [local irreducible] BitOracleMachine.run

private theorem insert_code (l : Fin CacheRoutineCode.insertSize) :
    program (insertLabel l) = TM2ReturnLink.redirect insertLabel 1 (CacheRoutineCode.insertCode l) := by
  simp only [program,insertLabel,show ¬5+l.val<5 by omega,↓reduceDIte,Nat.add_sub_cancel_left]

private def state (l : Option (Fin size)) (cache proposed key live history : List Bool)
    (bad : Bool) (tail counter previous : List Bool) (v : Fin 3 := 0) : Config :=
  ⟨l,v,![tail,[],[],[],counter,previous,[bad],proposed,key,cache,live,history]⟩

private theorem capture_step (cache proposed key live history tail counter previous : List Bool)
    (bad fresh : Bool) :
    tick (state (some 1) cache proposed key live history bad tail counter previous
      (if fresh then 2 else 1)) =
    state (some 2) cache proposed key live history (bad || !fresh) tail counter previous := by
  cases bad <;> cases fresh <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl

private def clearState (phase : Fin 3) (payload : List Bool)
    (cache proposed key live history : List Bool) (bad : Bool)
    (tail counter previous : List Bool) (v : Fin 3) : Config :=
  state (some ⟨2+phase.val,by have := Nat.pos_of_neZero CacheRoutineCode.insertSize; unfold size; omega⟩)
    cache proposed key live history bad
    (if phase=0 then payload else tail) (if phase=1 then payload else counter)
    (if phase=2 then payload else previous) v
private def clearResult (phase : Fin 3)
    (cache proposed key live history : List Bool) (bad : Bool)
    (tail counter previous : List Bool) : Config :=
  state (if phase=2 then none else some ⟨3+phase.val,by have := Nat.pos_of_neZero CacheRoutineCode.insertSize; unfold size; omega⟩)
    cache proposed key live history bad
    (if phase=0 then [] else tail) (if phase=1 then [] else counter)
    (if phase=2 then [] else previous) (if phase=2 then 2 else 0)
private theorem clear_cons (phase : Fin 3) (b : Bool) (bs : List Bool)
    (cache proposed key live history : List Bool) (bad : Bool)
    (tail counter previous : List Bool) (v : Fin 3) :
    tick (clearState phase (b::bs) cache proposed key live history bad tail counter previous v) =
    clearState phase bs cache proposed key live history bad tail counter previous (if b then 2 else 1) := by
  fin_cases phase <;> cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem clear_nil (phase : Fin 3)
    (cache proposed key live history : List Bool) (bad : Bool)
    (tail counter previous : List Bool) (v : Fin 3) :
    tick (clearState phase [] cache proposed key live history bad tail counter previous v) =
    clearResult phase cache proposed key live history bad tail counter previous := by
  fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem clear_run (phase : Fin 3) (payload : List Bool)
    (cache proposed key live history : List Bool) (bad : Bool)
    (tail counter previous : List Bool) (v : Fin 3) :
    tick^[payload.length+1] (clearState phase payload cache proposed key live history bad tail counter previous v) =
    clearResult phase cache proposed key live history bad tail counter previous := by
  induction payload generalizing v with
  | nil => simpa only [List.length_nil,zero_add,Function.iterate_one] using clear_nil phase cache proposed key live history bad tail counter previous v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,clear_cons,ih]

private theorem cleanup (cache proposed key live history tail counter previous : List Bool) (bad fresh : Bool) :
    tick^[previous.length+1+(counter.length+1+(tail.length+1+1))]
      (state (some 1) cache proposed key live history bad tail counter previous (if fresh then 2 else 1)) =
    result cache proposed key live history (bad || !fresh) := by
  have hc := capture_step cache proposed key live history tail counter previous bad fresh
  have h0 := clear_run 0 tail cache proposed key live history (bad || !fresh) [] counter previous 0
  have h1 := clear_run 1 counter cache proposed key live history (bad || !fresh) [] [] previous 0
  have h2 := clear_run 2 previous cache proposed key live history (bad || !fresh) [] [] [] 0
  rw [Function.iterate_add_apply tick (previous.length+1),
    Function.iterate_add_apply tick (counter.length+1),
    Function.iterate_add_apply tick (tail.length+1),Function.iterate_one,hc]
  change tick^[previous.length+1] (tick^[counter.length+1]
    (tick^[tail.length+1] (clearState 0 tail cache proposed key live history (bad || !fresh) [] counter previous 0))) = _
  rw [h0]
  change tick^[previous.length+1] (tick^[counter.length+1]
    (clearState 1 counter cache proposed key live history (bad || !fresh) [] [] previous 0)) = _
  rw [h1]
  change tick^[previous.length+1]
    (clearState 2 previous cache proposed key live history (bad || !fresh) [] [] [] 0) = _
  exact h2

private theorem finite_run (fuel : Nat) (src dst : CacheInsertMachine.Config)
    (frame : Fin 3 → List Bool) (h : CacheInsertMachine.tick^[fuel] src = dst) :
    (TM2ReturnLink.tick CacheRoutineCode.insertCode)^[fuel] (CacheRoutineCode.insertState src frame) =
      CacheRoutineCode.insertState dst frame := by
  unfold CacheRoutineCode.insertState CacheRoutineCode.insertCode
  rw [TM2FiniteCoordinates.run,TM2StackFrame.run]
  change _ = TM2FiniteCoordinates.present _ _ _ (TM2StackFrame.embed _ dst frame)
  rw [show (TM2ReturnLink.tick CacheInsertMachine.program)^[fuel] src = dst from h]

/-- The local instruction bound includes the collision capture and cleanup. -/
theorem local_cost (l : Fin size) : localCost (program l) ≤ 32 := by
  revert l
  decide +kernel

/-- The exact canonical input words determine the wrapper's numeric insertion cap. -/
def insertionFuel {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q)) : Nat :=
  CacheInsertMachine.cost p q cache.entries.length ((ballotCacheBitCodec p q).encode cache).length

def canonicalInputBound {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) (live history : List Bool) : Nat :=
  inputBound ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value)
    ((ballotKeyBitCodec p q).encode key) live history

def programmedCache {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q) :=
  if cache.lookup key = none then cache.insert key value else cache

/-- Complete canonical insertion, sticky collision capture, and cleanup of actual occupied residue. -/
theorem run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (live history : List Bool) (bad : Bool) :
    ∃ used ≤ clock (insertionFuel cache) (canonicalInputBound cache key value live history),
      tick^[used] (start ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value)
        ((ballotKeyBitCodec p q).encode key) live history bad) =
      result ((ballotCacheBitCodec p q).encode (programmedCache cache key value))
        ((primeScalarBitCodec q).encode value) ((ballotKeyBitCodec p q).encode key)
        live history (bad || !(cache.lookup key).isNone) := by
  let C := (ballotCacheBitCodec p q).encode cache
  let V := (primeScalarBitCodec q).encode value
  let K := (ballotKeyBitCodec p q).encode key
  let C' := (ballotCacheBitCodec p q).encode (programmedCache cache key value)
  let fresh := (cache.lookup key).isNone
  let initial := CacheRoutineCode.insertState (CacheInsertMachine.start K V C) ![[bad],live,history]
  have hi : ∃ fuel ≤ insertionFuel cache, ∃ tail counter previous,
      (TM2ReturnLink.tick CacheRoutineCode.insertCode)^[fuel] initial =
      ⟨none,if fresh then 2 else 1,![tail,[],[],[],counter,previous,[bad],V,K,C',live,history]⟩ := by
    cases found : cache.lookup key with
    | none =>
      obtain ⟨f,hf,hr⟩ := CacheInsertMachine.fresh_run cache key value found
      refine ⟨f,hf,[],[],[],?_⟩
      have he := finite_run f _ _ ![[bad],live,history] hr
      simp only [fresh,C',programmedCache,found,↓reduceIte,Option.isNone_none,↓reduceIte]
      refine he.trans ?_
      change (⟨_,_,_⟩ : BitOracleMachine.Config 12 CacheRoutineCode.insertSize 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    | some previousValue =>
      obtain ⟨f,hf,n,tail,hr⟩ := CacheInsertMachine.occupied_full_run cache key value previousValue found
      have hf' : f ≤ insertionFuel cache := by unfold insertionFuel CacheInsertMachine.cost; omega
      refine ⟨f,hf',tail,(n+1).bits,(primeScalarBitCodec q).encode previousValue,?_⟩
      have he := finite_run f _ _ ![[bad],live,history] hr
      simp only [fresh,C',programmedCache,found,reduceCtorEq,↓reduceIte,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
      refine he.trans ?_
      change (⟨_,_,_⟩ : BitOracleMachine.Config 12 CacheRoutineCode.insertSize 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
  obtain ⟨f,hf,tail,counter,previous,hi⟩ := hi
  have initial_words : initial.stk = ![C,[],[],[],[],[],[bad],V,K,[],live,history] := by
    funext k; fin_cases k <;> rfl
  have heightBound : TM2TapeRuns.height initial.stk ≤ canonicalInputBound cache key value live history := by
    rw [initial_words]
    unfold TM2TapeRuns.height
    apply Finset.sup_le
    intro k hk
    fin_cases k <;> change _ ≤ inputBound C V K live history
    all_goals dsimp [inputBound]; omega
  obtain ⟨u,huf,physical,growth⟩ := TM2TapeRuns.run_packed CacheRoutineCode.insertCode f initial
  rw [hi] at growth
  have hmul := Nat.mul_le_mul_right (TM2TapeRuns.codeAccesses CacheRoutineCode.insertCode) hf
  have ht : tail.length ≤ space (insertionFuel cache) (canonicalInputBound cache key value live history) :=
    (growth 0).trans (Nat.add_le_add heightBound hmul)
  have hn : counter.length ≤ space (insertionFuel cache) (canonicalInputBound cache key value live history) :=
    (growth 4).trans (Nat.add_le_add heightBound hmul)
  have hp : previous.length ≤ space (insertionFuel cache) (canonicalInputBound cache key value live history) :=
    (growth 5).trans (Nat.add_le_add heightBound hmul)
  obtain ⟨steps,hsteps,he⟩ := TM2ReturnLink.run CacheRoutineCode.insertCode program insertLabel 1
    insert_code f initial (by rw [hi])
  rw [hi] at he
  have entry : tick (start C V K live history bad) = TM2ReturnLink.embed insertLabel 1 initial := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have returned : TM2ReturnLink.embed insertLabel 1
      (⟨none,if fresh then 2 else 1,![tail,[],[],[],counter,previous,[bad],V,K,C',live,history]⟩ :
        BitOracleMachine.Config 12 CacheRoutineCode.insertSize 3) =
      state (some 1) C' V K live history bad tail counter previous (if fresh then 2 else 1) := rfl
  rw [returned] at he
  change tick^[steps] _ = _ at he
  have initial_run : tick^[steps+1] (start C V K live history bad) =
      state (some 1) C' V K live history bad tail counter previous (if fresh then 2 else 1) := by
    rw [Function.iterate_succ_apply,entry,he]
  refine ⟨previous.length+1+(counter.length+1+(tail.length+1+1))+(steps+1),?_,?_⟩
  · unfold clock
    omega
  · rw [Function.iterate_add_apply,initial_run,cleanup]

/-- Only an actual halted run is padded to the fixed canonical clock. -/
theorem padded_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (live history : List Bool) (bad : Bool) :
      tick^[clock (insertionFuel cache) (canonicalInputBound cache key value live history)]
        (start ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value)
        ((ballotKeyBitCodec p q).encode key) live history bad) =
      result ((ballotCacheBitCodec p q).encode (programmedCache cache key value))
        ((primeScalarBitCodec q).encode value) ((ballotKeyBitCodec p q).encode key)
        live history (bad || !(cache.lookup key).isNone) := by
  obtain ⟨u,hu,he⟩ := run cache key value live history bad
  rw [show clock (insertionFuel cache) (canonicalInputBound cache key value live history) =
    (clock (insertionFuel cache) (canonicalInputBound cache key value live history)-u)+u by omega,
    Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result _ _ _ _ _ _) = _ from rfl) _

theorem clock_mono {I J H H' : Nat} (hI : I ≤ J) (hH : H ≤ H') : clock I H ≤ clock J H' := by
  unfold clock space
  exact Nat.add_le_add_right (Nat.add_le_add hI (Nat.mul_le_mul_left 3
    (Nat.add_le_add hH (Nat.mul_le_mul_right _ hI)))) 5

/-- Derived charge at source-derived enclosing bounds; no cost correspondence is assumed. -/
theorem charged_bounded {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (live history : List Bool) (bad : Bool) (I H : Nat)
    (hI : insertionFuel cache ≤ I) (hH : canonicalInputBound cache key value live history ≤ H) :
    ∃ charge ≤ cost I H,
      BitOracleMachine.run code (clock I H)
        (start ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value)
        ((ballotKeyBitCodec p q).encode key) live history bad) =
      pure (result ((ballotCacheBitCodec p q).encode (programmedCache cache key value))
        ((primeScalarBitCodec q).encode value) ((ballotKeyBitCodec p q).encode key)
        live history (bad || !(cache.lookup key).isNone),charge) := by
  obtain ⟨u,hu,he⟩ := run cache key value live history bad
  have hu' := hu.trans (clock_mono hI hH)
  have hp : tick^[clock I H] (start ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value)
        ((ballotKeyBitCodec p q).encode key) live history bad) =
      result ((ballotCacheBitCodec p q).encode (programmedCache cache key value))
        ((primeScalarBitCodec q).encode value) ((ballotKeyBitCodec p q).encode key)
        live history (bad || !(cache.lookup key).isNone) := by
    rw [show clock I H=(clock I H-u)+u by omega,Function.iterate_add_apply,he]
    exact Function.iterate_fixed (show tick (result _ _ _ _ _ _) = _ from rfl) _
  obtain ⟨charge,hc,hr⟩ := compute_run_cost program 32 local_cost (clock I H) _
  rw [show (TM2ReturnLink.tick program)^[clock I H] _ = _ from hp] at hr
  exact ⟨charge,hc,hr⟩

/-- Canonical input derives both numeric bounds, without caller premises. -/
theorem charged {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q)) (value : ZMod q)
    (live history : List Bool) (bad : Bool) :
    ∃ charge ≤ cost (insertionFuel cache) (canonicalInputBound cache key value live history),
      BitOracleMachine.run code (clock (insertionFuel cache) (canonicalInputBound cache key value live history))
        (start ((ballotCacheBitCodec p q).encode cache) ((primeScalarBitCodec q).encode value)
        ((ballotKeyBitCodec p q).encode key) live history bad) =
      pure (result ((ballotCacheBitCodec p q).encode (programmedCache cache key value))
        ((primeScalarBitCodec q).encode value) ((ballotKeyBitCodec p q).encode key)
        live history (bad || !(cache.lookup key).isNone),charge) :=
  charged_bounded cache key value live history bad _ _ le_rfl le_rfl

#print axioms insert_code
#print axioms capture_step
#print axioms cleanup
#print axioms finite_run
#print axioms run
#print axioms padded_run
#print axioms clock_mono
#print axioms charged_bounded
#print axioms charged
end ExplainableCrypto.Helios.Computational.CacheProgrammedInsertMachine
