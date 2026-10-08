import ExplainableCrypto.Helios.Computational.PrimeNoncePairTransport

/-! Full-state execution and derived charge for resident nonce-pair transport. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNoncePairTransport
open Turing.TM2 OracleComp BitOracleMachine
set_option maxRecDepth 8192

private def copyActive (which : Fin 2) (phase : Option Bool) (xs ys zs : List Bool)
    (frame : Fin 8 → List Bool) (v : Fin 3 := 0) : Config 11 size 3 :=
  ⟨some (phase.elim (copyReturn which) (fun b => copyLabel which (if b then 1 else 0))),v,
    if which = 0 then ![zs,frame 0,frame 1,frame 2,ys,frame 3,frame 4,frame 5,xs,frame 6,frame 7]
    else ![zs,frame 0,frame 1,frame 2,frame 3,xs,frame 4,frame 5,frame 6,ys,frame 7]⟩
private theorem copy_collect_step (which : Fin 2) (b : Bool) (xs ys zs : List Bool) (frame : Fin 8 → List Bool) (v : Fin 3) :
    BitOracleMachine.step code (copyActive which (some false) (b::xs) ys zs frame v) =
      pure (copyActive which (some false) xs ys (b::zs) frame (CoinWordLoader.encode (some b)),4) := by
  fin_cases which <;> cases b <;> apply congrArg pure
  all_goals change ((⟨_,_,_⟩ : Config 11 size 3),4) = (⟨_,_,_⟩,4); congr 2
  all_goals funext k; fin_cases k <;> rfl
private theorem copy_collect_empty (which : Fin 2) (ys zs : List Bool) (frame : Fin 8 → List Bool) (v : Fin 3) :
    BitOracleMachine.step code (copyActive which (some false) [] ys zs frame v) =
      pure (copyActive which (some true) [] ys zs frame,4) := by
  fin_cases which <;> apply congrArg pure
  all_goals change ((⟨_,_,_⟩ : Config 11 size 3),4) = (⟨_,_,_⟩,4)
  all_goals congr 2; funext k; fin_cases k <;> rfl
private theorem copy_restore_step (which : Fin 2) (b : Bool) (xs ys zs : List Bool) (frame : Fin 8 → List Bool) (v : Fin 3) :
    BitOracleMachine.step code (copyActive which (some true) xs ys (b::zs) frame v) =
      pure (copyActive which (some true) (b::xs) (b::ys) zs frame (CoinWordLoader.encode (some b)),5) := by
  fin_cases which <;> cases b <;> apply congrArg pure
  all_goals change ((⟨_,_,_⟩ : Config 11 size 3),5) = (⟨_,_,_⟩,5); congr 2
  all_goals funext k; fin_cases k <;> rfl
private theorem copy_restore_empty (which : Fin 2) (xs ys : List Bool) (frame : Fin 8 → List Bool) (v : Fin 3) :
    BitOracleMachine.step code (copyActive which (some true) xs ys [] frame v) =
      pure (copyActive which none xs ys [] frame,5) := by
  fin_cases which <;> apply congrArg pure
  all_goals change ((⟨_,_,_⟩ : Config 11 size 3),5) = (⟨_,_,_⟩,5)
  all_goals congr 2; funext k; fin_cases k <;> rfl


private theorem copy_collect (which : Fin 2) (xs ys zs : List Bool) (frame : Fin 8 → List Bool) (v : Fin 3) :
    run code (xs.length+1) (copyActive which (some false) xs ys zs frame v) =
      pure (copyActive which (some true) [] ys (xs.reverse++zs) frame,4*(xs.length+1)) := by
  induction xs generalizing zs v with
  | nil => simp [run,copy_collect_empty]
  | cons b xs ih =>
    rw [List.length_cons,Nat.add_assoc,run,copy_collect_step,pure_bind,ih,pure_bind]
    simp [List.reverse_cons,List.append_assoc,Nat.mul_add]
    omega

private theorem copy_restore (which : Fin 2) (xs ys zs : List Bool) (frame : Fin 8 → List Bool) (v : Fin 3) :
    run code (zs.length+1) (copyActive which (some true) xs ys zs frame v) =
      pure (copyActive which none (zs.reverse++xs) (zs.reverse++ys) [] frame,5*(zs.length+1)) := by
  induction zs generalizing xs ys v with
  | nil => simp [run,copy_restore_empty]
  | cons b zs ih =>
    rw [List.length_cons,Nat.add_assoc,run,copy_restore_step,pure_bind,ih,pure_bind]
    simp [List.reverse_cons,List.append_assoc,Nat.mul_add]
    omega

private theorem copy_resident (which : Fin 2) (word : List Bool) (frame : Fin 8 → List Bool) (v : Fin 3) :
    run code (2*word.length+2) (copyActive which (some false) word [] [] frame v) =
      pure (copyActive which none word word [] frame,9*(word.length+1)) := by
  rw [show 2*word.length+2 = (word.length+1)+(word.length+1) by omega,
    BitOracleReturnLink.run_add,copy_collect,pure_bind]
  simp only [List.append_nil]
  have hr := copy_restore which [] [] word.reverse frame 0
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  rw [hr,pure_bind]
  congr 2
  omega

private theorem clear_run (port : Fin 11) (again next : Fin size)
    (hcode : code again = .compute (clear port again next))
    (word : List Bool) (other : Fin 11 → List Bool) (memory : Fin 3) :
    run code (word.length+1) ⟨some again,memory,Function.update other port word⟩ =
      pure (⟨some next,0,Function.update other port []⟩,4*(word.length+1)) := by
  induction word generalizing memory with
  | nil =>
    simp [run,BitOracleMachine.step,hcode,clear,enter,stepAux,CoinWordLoader.encode,localCost]
  | cons bit word ih =>
    rw [List.length_cons,run]
    cases bit <;>
      simp [BitOracleMachine.step,hcode,clear,enter,stepAux,CoinWordLoader.encode,
        localCost,ih,Nat.mul_add,Nat.add_comm]


private theorem entry_exact (record savedNonce context : List Bool) :
    run code (entryClock record) (entryStart record savedNonce context) =
      pure (ready record savedNonce context,entryCost record) := by
  let frame : Fin 8 → List Bool := ![[],[],[],[],[],[],savedNonce,context]
  have first := copy_resident 0 record frame 0
  have hi : copyActive 0 (some false) record [] [] frame 0 = entryStart record savedNonce context := by
    change (⟨_,_,_⟩ : Config 11 size 3) = ⟨_,_,_⟩
    congr 1
  have last : run code 1 (copyActive 0 none record record [] frame) =
      pure (ready record savedNonce context,2) := by
    change (pure ((⟨none,0,_⟩ : Config 11 size 3),2) : OracleComp spec _) = _
    congr 2
  rw [hi] at first
  rw [show entryClock record = (2*record.length+2)+1 by unfold entryClock; omega,
    BitOracleReturnLink.run_add,first,pure_bind,last,pure_bind]
  rfl

/-- Actual record reload preserves both saved words and clears every work port
except the sampler input. Its charge is derived from all executed copy steps. -/
theorem entry_run (record savedNonce context : List Bool) :
    ∃ charge ≤ entryCost record,
      run code (entryClock record) (entryStart record savedNonce context) =
        pure (ready record savedNonce context,charge) :=
  ⟨entryCost record,le_rfl,entry_exact record savedNonce context⟩

/-- Actual first-nonce retention, cleanup of sampler work and record reload.
The complete 11-port successor and exact clock require no caller certificate. -/
theorem between_run (record modulus nonce context : List Bool) :
    ∃ charge ≤ betweenCost record modulus nonce,
      run code (betweenClock record modulus nonce) (betweenStart record modulus nonce context) =
        pure (ready record nonce context,charge) := by
  let frame : Fin 8 → List Bool := ![modulus,[],[],[],[],[],record,context]
  have first := copy_resident 1 nonce frame 2
  have hi : copyActive 1 (some false) nonce [] [] frame 2 = betweenStart record modulus nonce context := by
    change (⟨_,_,_⟩ : Config 11 size 3) = ⟨_,_,_⟩
    congr 1
  rw [hi] at first
  let middle : Config 11 size 3 :=
    ⟨some 6,0,![[],modulus,[],[],[],[],[],[],record,nonce,context]⟩
  have second : run code (nonce.length+1) (copyActive 1 none nonce nonce [] frame) =
      pure (middle,4*(nonce.length+1)) := by
    have h := clear_run 5 5 6 rfl nonce middle.stk 0
    have hs : (⟨some 5,0,Function.update middle.stk 5 nonce⟩ : Config 11 size 3) =
        copyActive 1 none nonce nonce [] frame := by
      change (⟨_,_,_⟩ : Config 11 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have he : (⟨some 6,0,Function.update middle.stk 5 []⟩ : Config 11 size 3) = middle := by
      change (⟨_,_,_⟩ : Config 11 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    rwa [hs,he] at h
  have third : run code (modulus.length+1) middle =
      pure (entryStart record nonce context,4*(modulus.length+1)) := by
    have h := clear_run 1 6 0 rfl modulus (entryStart record nonce context).stk 0
    have hs : (⟨some 6,0,Function.update (entryStart record nonce context).stk 1 modulus⟩ : Config 11 size 3) = middle := by
      change (⟨_,_,_⟩ : Config 11 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have he : (⟨some 0,0,Function.update (entryStart record nonce context).stk 1 []⟩ : Config 11 size 3) = entryStart record nonce context := by
      change (⟨_,_,_⟩ : Config 11 size 3) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    rwa [hs,he] at h
  refine ⟨betweenCost record modulus nonce,le_rfl,?_⟩
  unfold betweenClock
  rw [BitOracleReturnLink.run_add,BitOracleReturnLink.run_add,BitOracleReturnLink.run_add,
    first,pure_bind,second,pure_bind,pure_bind,third,pure_bind,pure_bind,entry_exact,pure_bind]
  rfl

/-- Literal nonpalindromic record and distinct saved words retain their order. -/
theorem entry_control :
    run code 9 (entryStart [false,true,true] [true,false] [true,true,false]) =
      pure ((⟨none,0,![[],[],[],[],[false,true,true],[],[],[],[false,true,true],
        [true,false],[true,true,false]]⟩ : Config 11 size 3),38) := by
  exact entry_exact [false,true,true] [true,false] [true,true,false]

/-- The first sampled nonce is retained while the old modulus and answer work
are removed. The expected full state is independently literal. -/
theorem between_control :
    Prod.fst <$> run code 27
      (betweenStart [false,true,true] [true,false] [true,false,true,true] [true,true,false]) =
      pure (⟨none,0,![[],[],[],[],[false,true,true],[],[],[],[false,true,true],
        [true,false,true,true],[true,true,false]]⟩ : Config 11 size 3) := by
  obtain ⟨charge,_,h⟩ := between_run [false,true,true] [true,false] [true,false,true,true] [true,true,false]
  change run code 27 _ = _ at h
  rw [h]
  rfl

private def omitNonceCopy : Code 11 size 3 := fun l =>
  if l = 3 then .compute (.goto (fun _ => 5)) else code l

attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
/-- The smallest nonempty nonce is lost when the actual nonce-copy entry jumps
straight to cleanup. This is a semantic failure even without observing charges. -/
theorem omission_control :
    Prod.fst <$> run omitNonceCopy 10 (betweenStart [] [] [true] []) =
      pure (⟨none,0,fun _ => []⟩ : Config 11 size 3) := by
  change (pure (⟨none,0,_⟩ : Config 11 size 3) : OracleComp spec _) = _
  congr 2
  funext k
  fin_cases k <;> rfl

/-- Correct code retains the nonce on the same minimized input. -/
theorem omission_not_correct :
    (fun out => out.1.stk 9) <$> run code 10 (betweenStart [] [] [true] []) ≠ pure [] := by
  obtain ⟨charge,_,h⟩ := between_run [] [] [true] []
  change run code 10 _ = _ at h
  rw [h]
  simp [ready]

#print axioms entry_run
#print axioms between_run
#print axioms entry_control
#print axioms between_control
#print axioms omission_control
#print axioms omission_not_correct

end ExplainableCrypto.Helios.Computational.PrimeNoncePairTransport
