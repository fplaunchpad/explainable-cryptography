import ExplainableCrypto.Helios.Computational.CacheCallerMachine

/-! Executed resident entry and guarded return for the original request. -/
namespace ExplainableCrypto.Helios.Computational.CacheCallerMachine
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 8192
attribute [local irreducible] CacheHashDispatch.code CacheHashDispatch.requestClock
  CacheHashDispatch.requestCost

private theorem request_code (label : Fin CacheHashDispatch.size) : localCode (requestLabel label) =
    BitOracleReturnLink.command requestLabel (some returnLabel) (CacheHashDispatch.code label) := by
  have h0 : ¬ (requestLabel label).val < 3 := by simp only [requestLabel]; omega
  have h1 : ¬ (requestLabel label).val < 5 := by simp only [requestLabel]; omega
  rw [localCode,dif_neg h0,dif_neg h1]
  simp [requestLabel]

private def copyActive (phase : Option Bool) (xs ys zs : List Bool)
    (frame : Fin 9 → List Bool) (v : Fin 3 := 0) : Config 12 size 3 :=
  ⟨some (phase.elim 1 (fun b => copyLabel (if b then 1 else 0))),v,
    ![ys,frame 0,zs,frame 1,frame 2,frame 3,frame 4,frame 5,frame 6,xs,frame 7,frame 8]⟩
private theorem copy_collect_step (b : Bool) (xs ys zs : List Bool) (frame : Fin 9 → List Bool) (v : Fin 3) :
    BitOracleMachine.step localCode (copyActive (some false) (b::xs) ys zs frame v) =
      pure (copyActive (some false) xs ys (b::zs) frame (CoinWordLoader.encode (some b)),4) := by
  cases b <;> apply congrArg pure <;>
    change ((⟨_,_,_⟩ : Config 12 size 3),4) = (⟨_,_,_⟩,4) <;> congr 2
  all_goals funext k; fin_cases k <;> rfl
private theorem copy_collect_empty (ys zs : List Bool) (frame : Fin 9 → List Bool) (v : Fin 3) :
    BitOracleMachine.step localCode (copyActive (some false) [] ys zs frame v) =
      pure (copyActive (some true) [] ys zs frame,4) := by
  apply congrArg pure
  change ((⟨_,_,_⟩ : Config 12 size 3),4) = (⟨_,_,_⟩,4)
  congr 2
  funext k; fin_cases k <;> rfl
private theorem copy_restore_step (b : Bool) (xs ys zs : List Bool) (frame : Fin 9 → List Bool) (v : Fin 3) :
    BitOracleMachine.step localCode (copyActive (some true) xs ys (b::zs) frame v) =
      pure (copyActive (some true) (b::xs) (b::ys) zs frame (CoinWordLoader.encode (some b)),5) := by
  cases b <;> apply congrArg pure <;>
    change ((⟨_,_,_⟩ : Config 12 size 3),5) = (⟨_,_,_⟩,5) <;> congr 2
  all_goals funext k; fin_cases k <;> rfl
private theorem copy_restore_empty (xs ys : List Bool) (frame : Fin 9 → List Bool) (v : Fin 3) :
    BitOracleMachine.step localCode (copyActive (some true) xs ys [] frame v) =
      pure (copyActive none xs ys [] frame,5) := by
  apply congrArg pure
  change ((⟨_,_,_⟩ : Config 12 size 3),5) = (⟨_,_,_⟩,5)
  congr 2
  funext k; fin_cases k <;> rfl


private theorem copy_collect (xs ys zs : List Bool) (frame : Fin 9 → List Bool) (v : Fin 3) :
    run localCode (xs.length+1) (copyActive (some false) xs ys zs frame v) =
      pure (copyActive (some true) [] ys (xs.reverse++zs) frame,4*(xs.length+1)) := by
  induction xs generalizing zs v with
  | nil => simp [run,copy_collect_empty]
  | cons b xs ih =>
    rw [List.length_cons,Nat.add_assoc,run,copy_collect_step,pure_bind,ih,pure_bind]
    simp [List.reverse_cons,List.append_assoc,Nat.mul_add]
    omega

private theorem copy_restore (xs ys zs : List Bool) (frame : Fin 9 → List Bool) (v : Fin 3) :
    run localCode (zs.length+1) (copyActive (some true) xs ys zs frame v) =
      pure (copyActive none (zs.reverse++xs) (zs.reverse++ys) [] frame,5*(zs.length+1)) := by
  induction zs generalizing xs ys v with
  | nil => simp [run,copy_restore_empty]
  | cons b zs ih =>
    rw [List.length_cons,Nat.add_assoc,run,copy_restore_step,pure_bind,ih,pure_bind]
    simp [List.reverse_cons,List.append_assoc,Nat.mul_add]
    omega

private theorem copy_resident (word : List Bool) (frame : Fin 9 → List Bool) :
    run localCode (2*word.length+2) (copyActive (some false) word [] [] frame) =
      pure (copyActive none word word [] frame,9*(word.length+1)) := by
  rw [show 2*word.length+2 = (word.length+1)+(word.length+1) by omega,
    BitOracleReturnLink.run_add,copy_collect,pure_bind]
  simp only [List.append_nil]
  have hr := copy_restore [] [] word.reverse frame 0
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  rw [hr,pure_bind]
  congr 2
  omega

private theorem clear_run (port : Fin 12) (again next : Fin size)
    (hcode : localCode again = .compute (clear port again next))
    (word : List Bool) (other : Fin 12 → List Bool) (memory : Fin 3) :
    run localCode (word.length+1) ⟨some again,memory,Function.update other port word⟩ =
      pure (⟨some next,0,Function.update other port []⟩,4*(word.length+1)) := by
  induction word generalizing memory with
  | nil =>
    simp [run,BitOracleMachine.step,hcode,clear,enter,stepAux,CoinWordLoader.encode,localCost]
  | cons bit word ih =>
    rw [List.length_cons,run]
    cases bit <;>
      simp [BitOracleMachine.step,hcode,clear,enter,stepAux,CoinWordLoader.encode,
        localCost,ih,Nat.mul_add,Nat.add_comm]

private theorem load_local (key cache log record previous : List Bool) :
    ∃ charge ≤ loadCost cache previous,
      run localCode (loadClock cache previous) (localStart key cache log record previous) =
        pure (BitOracleReturnLink.embed requestLabel (some returnLabel)
          (CacheHashDispatch.start key cache log record),charge) := by
  let frame : Fin 9 → List Bool := ![[],[],[],[],[],[],key,log,record]
  have first : run localCode (previous.length+1) (localStart key cache log record previous) =
      pure (copyActive (some false) cache [] [] frame,4*(previous.length+1)) := by
    have h := clear_run 7 0 (copyLabel 0) rfl previous
      (localStart key cache log record []).stk 0
    have hi : (⟨some 0,0,Function.update (localStart key cache log record []).stk 7 previous⟩ : Config 12 size 3) =
        localStart key cache log record previous := by
      change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have hf : (⟨some (copyLabel 0),0,Function.update (localStart key cache log record []).stk 7 []⟩ : Config 12 size 3) =
        copyActive (some false) cache [] [] frame := by
      change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    rwa [hi,hf] at h
  have last : run localCode (cache.length+1) (copyActive none cache cache [] frame) =
      pure (BitOracleReturnLink.embed requestLabel (some returnLabel)
        (CacheHashDispatch.start key cache log record),4*(cache.length+1)) := by
    have h := clear_run 9 1 (requestLabel 0) rfl cache
      (CacheHashDispatch.start key cache log record).stk 0
    have hi : (⟨some 1,0,Function.update (CacheHashDispatch.start key cache log record).stk 9 cache⟩ : Config 12 size 3) =
        copyActive none cache cache [] frame := by
      change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have hf : (⟨some (requestLabel 0),0,Function.update (CacheHashDispatch.start key cache log record).stk 9 []⟩ : Config 12 size 3) =
        BitOracleReturnLink.embed requestLabel (some returnLabel) (CacheHashDispatch.start key cache log record) := by
      change (⟨_,_,_⟩ : Config 12 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    rwa [hi,hf] at h
  refine ⟨4*(previous.length+1)+9*(cache.length+1)+4*(cache.length+1),?_,?_⟩
  · unfold loadCost; omega
  · unfold loadClock
    rw [BitOracleReturnLink.run_add,BitOracleReturnLink.run_add,first,pure_bind,
      copy_resident,pure_bind,pure_bind,last,pure_bind]

/-- Actual entry from resident words, including the old answer and saved caller
data. The original cache is moved into probe work, all local scratch is derived
empty, and the clock ends exactly at the live dispatcher entry. -/
theorem load_request (key cache log record previous saved : List Bool) :
    ∃ charge ≤ loadCost cache previous,
      run code (loadClock cache previous) (start key cache log record previous saved) =
        pure (ready key cache log record saved,charge) := by
  obtain ⟨charge,hc,he⟩ := load_local key cache log record previous
  refine ⟨charge,hc,?_⟩
  rw [code,start,BitOracleStackFrame.run,he,map_pure]
  rfl


private theorem gate_run (cfg : Config 12 CacheHashDispatch.size 3)
    (hh : cfg.l = none) (hv : cfg.var = 2) :
    run localCode 1 (BitOracleReturnLink.embed requestLabel (some returnLabel) cfg) =
      pure (BitOracleReturnLink.embed requestLabel none cfg,3) := by
  rcases cfg with ⟨label,v,words⟩
  dsimp only at hh hv
  subst label; subst v
  rfl

private theorem request_success {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat)
    (out : Config 12 CacheHashDispatch.size 3)
    (ho : out ∈ support (CacheHashDispatch.request cache key log slack)) :
    out.l = none ∧ out.var = 2 := by
  cases h : cache.lookup key with
  | some a =>
    simp only [CacheHashDispatch.request,h,mem_support_pure_iff] at ho
    subst out
    exact ⟨rfl,rfl⟩
  | none =>
    simp only [CacheHashDispatch.request,h] at ho
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ ho
    exact ⟨rfl,rfl⟩

private theorem request_linked {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) :
    let initial := CacheHashDispatch.start ((ballotKeyBitCodec p q).encode key)
      ((ballotCacheBitCodec p q).encode cache) (((ballotLogEntryBitCodec p q).list).encode log)
      (SamplerOperands.input slack q [])
    run localCode (CacheHashDispatch.requestClock cache key log slack+1)
      (BitOracleReturnLink.embed requestLabel (some returnLabel) initial) =
      (fun out => (BitOracleReturnLink.embed requestLabel none out.1,out.2+3)) <$>
        run CacheHashDispatch.code (CacheHashDispatch.requestClock cache key log slack) initial := by
  dsimp only
  let initial := CacheHashDispatch.start ((ballotKeyBitCodec p q).encode key)
    ((ballotCacheBitCodec p q).encode cache) (((ballotLogEntryBitCodec p q).list).encode log)
    (SamplerOperands.input slack q [])
  let D := run CacheHashDispatch.code (CacheHashDispatch.requestClock cache key log slack) initial
  have hd := CacheHashDispatch.request_run cache key log slack
  have good (out) (ho : out ∈ support D) : out.1.l = none ∧ out.1.var = 2 := by
    apply request_success cache key log slack out.1
    rw [← hd.1,support_map]
    exact ⟨out,ho,rfl⟩
  have tail (out) (ho : out ∈ support D) :
      run localCode 1 (BitOracleReturnLink.embed requestLabel (some returnLabel) out.1) =
        pure (BitOracleReturnLink.embed requestLabel none out.1,3) :=
    gate_run out.1 (good out ho).1 (good out ho).2
  have hc : ∀ out ∈ support D,
      ∀ last ∈ support (run localCode 1 (BitOracleReturnLink.embed requestLabel (some returnLabel) out.1)),
        last.1.l = none := by
    intro out ho last hl
    rw [tail out ho,mem_support_pure_iff] at hl
    subst last
    simp [BitOracleReturnLink.embed,(good out ho).1]
  rw [BitOracleReturnLink.run CacheHashDispatch.code localCode requestLabel returnLabel request_code
    _ 1 initial (fun out ho => (good out ho).1) hc]
  rw [map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro out ho
  rw [tail out ho,pure_bind]
  rfl

attribute [local irreducible] localCode code clock cost

/-- The resident caller executes loading, the whole original request and the
actual return guard with its saved word intact. It derives termination and the
combined local charge; source operand production and continuation arithmetic
are not assumed to have been compiled by this theorem. -/
theorem request_run {p q : Nat} [NeZero p] [NeZero q]
    (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat)
    (previous saved : List Bool) :
    let execution := run code (clock cache key log slack previous)
      (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
        (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []) previous saved)
    (Prod.fst <$> execution = (fun cfg => result cfg saved) <$> CacheHashDispatch.request cache key log slack) ∧
      ∀ out ∈ support execution, out.1.l = none ∧ out.2 ≤ cost cache key log slack previous := by
  dsimp only
  let K := (ballotKeyBitCodec p q).encode key
  let C := (ballotCacheBitCodec p q).encode cache
  let L := ((ballotLogEntryBitCodec p q).list).encode log
  let R := SamplerOperands.input slack q []
  let D := run CacheHashDispatch.code (CacheHashDispatch.requestClock cache key log slack)
    (CacheHashDispatch.start K C L R)
  obtain ⟨loaded,hl,he⟩ := load_local K C L R previous
  have hr : run code (clock cache key log slack previous) (start K C L R previous saved) =
      (fun out => (result out.1 saved,loaded+(out.2+3))) <$> D := by
    rw [code,start,BitOracleStackFrame.run,clock,BitOracleReturnLink.run_add,he,pure_bind,request_linked]
    simp [map_eq_bind_pure_comp,bind_assoc,result,D,K,C,L,R]
  rw [hr]
  have hd := CacheHashDispatch.request_run cache key log slack
  constructor
  · have h := congrArg (fun oa => (fun cfg => result cfg saved) <$> oa) hd.1
    simpa only [Functor.map_map,Function.comp_def,D,K,C,L,R] using h
  · intro out ho
    obtain ⟨d,hd',rfl⟩ := mem_support_map_peel _ _ ho
    have hh := hd.2 d hd'
    constructor
    · simp [result,BitOracleStackFrame.embed,TM2StackFrame.embed,BitOracleReturnLink.embed,hh.1]
    · unfold cost
      dsimp only [C] at hl ⊢
      omega

#print axioms load_request
#print axioms request_run

end ExplainableCrypto.Helios.Computational.CacheCallerMachine
