import ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

def cleanWords (old : Fin 44 → List Bool) : Fin 48 → List Bool :=
  fun k => if 23 ≤ k.val ∧ k.val < 28 then [] else initialWords old k

def words (old : Fin 44 → List Bool) (a b shadow live flag history : List Bool) : Fin 48 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (cleanWords old) 23 a) 26 b)
      44 shadow) 45 live) 46 flag) 47 history

def state (l : Option (Fin size)) (old : Fin 44 → List Bool)
    (a b shadow live flag history : List Bool) (v : Fin 3 := 0) : Config :=
  ⟨l,v,words old a b shadow live flag history⟩

def framedWord (payload suffix : List Bool) := uniformNatEncode payload.length ++ (payload++suffix)

def beforeField (phase : Fin 11) (old : Fin 44 → List Bool)
    (payload suffix a b shadow live flag history : List Bool) : Config :=
  let f := framedWord payload suffix
  state (some (fieldLabel phase 0)) old
    (![f,f,f,f,f,[],a,f,f,a,a] phase)
    (![[],[],[],[],[],f,f,b,[],f,f] phase)
    (![shadow,shadow,shadow,shadow,shadow,shadow,shadow,[],shadow,shadow,shadow] phase)
    (![live,live,live,live,live,live,[],live,live,live,live] phase)
    (![flag,flag,flag,flag,flag,flag,flag,flag,flag,[],flag] phase)
    (![history,history,history,history,history,history,history,history,history,history,[]] phase)

def afterField (phase : Fin 11) (old : Fin 44 → List Bool)
    (payload suffix a b shadow live flag history : List Bool) : Config :=
  state (some (fieldReturn phase)) old
    (![suffix,suffix,suffix,suffix,suffix,payload,a,suffix,suffix,a,a] phase)
    (![payload,payload,payload,payload,payload,suffix,suffix,b,payload,suffix,suffix] phase)
    (![shadow,shadow,shadow,shadow,shadow,shadow,shadow,payload,shadow,shadow,shadow] phase)
    (![live,live,live,live,live,live,payload,live,live,live,live] phase)
    (![flag,flag,flag,flag,flag,flag,flag,flag,flag,payload,flag] phase)
    (![history,history,history,history,history,history,history,history,history,history,payload] phase) 2
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

theorem field_code (phase : Fin 11) (l : Fin 9) : program (fieldLabel phase l) =
    TM2ReturnLink.redirect (fieldLabel phase) (fieldReturn phase) (fieldProgram phase l) := by
  fin_cases phase <;> fin_cases l <;> rfl

theorem field_run (phase : Fin 11)
    (old : Fin 44 → List Bool)
    (payload suffix a b shadow live flag history : List Bool) :
    ∃ used ≤ fieldClock payload.length,
      tick^[used] (beforeField phase old payload suffix a b shadow live flag history) =
        afterField phase old payload suffix a b shadow live flag history := by
  let source := FieldPrefixMachine.start (framedWord payload suffix)
  let target : FieldPrefixMachine.Config :=
    ⟨none,some true,(FieldReadMachine.config none payload [] suffix [] (some true)).stk⟩
  let frame : Fin 44 → List Bool := fun k =>
    (beforeField phase old payload suffix a b shadow live flag history).stk (fieldLayout phase (.inr k))
  obtain ⟨fuel,hfuel,hi⟩ := RecordFieldStepMachine.field_complete payload suffix
  change FieldPrefixMachine.tick^[fuel] source = target at hi
  have hf := TM2StackFrame.run (fieldLayout phase) FieldPrefixMachine.program fuel source frame
  change _ = TM2StackFrame.embed (fieldLayout phase) (FieldPrefixMachine.tick^[fuel] source) frame at hf
  rw [hi] at hf
  have hc := TM2FiniteCoordinates.run (Equiv.refl (Fin 48)) CacheRequestInput.labels BinaryModuloCode.memory
    (fun l => TM2StackFrame.relocate (fieldLayout phase) (FieldPrefixMachine.program l)) fuel
    (TM2StackFrame.embed (fieldLayout phase) source frame)
  rw [hf] at hc
  change (TM2ReturnLink.tick (fieldProgram phase))^[fuel] _ = _ at hc
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run (fieldProgram phase) program (fieldLabel phase) (fieldReturn phase)
    (field_code phase) fuel _ (by rw [hc]; rfl)
  rw [hc] at he
  have hs : TM2ReturnLink.embed (fieldLabel phase) (fieldReturn phase)
      (TM2FiniteCoordinates.present (Equiv.refl _) CacheRequestInput.labels BinaryModuloCode.memory
        (TM2StackFrame.embed (fieldLayout phase) source frame)) =
      beforeField phase old payload suffix a b shadow live flag history := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed (fieldLabel phase) (fieldReturn phase)
      (TM2FiniteCoordinates.present (Equiv.refl _) CacheRequestInput.labels BinaryModuloCode.memory
        (TM2StackFrame.embed (fieldLayout phase) target frame)) =
      afterField phase old payload suffix a b shadow live flag history := by
    fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    all_goals congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu.trans hfuel,by rwa [hs,ht] at he⟩

#print axioms field_run
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private theorem copy_code (l : Fin 2) : program (copyLabel l) =
    TM2ReturnLink.redirect copyLabel 17 (copyProgram l) := by fin_cases l <;> rfl

private theorem sequence {a b c : Config} {n k : Nat}
    (h : tick^[n] a = b) (h' : tick^[k] b = c) : tick^[k+n] a = c := by
  rw [Function.iterate_add_apply,h,h']

private theorem entry (old : Fin 44 → List Bool)
    (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    tick (start old) = state (some (copyLabel 0)) old [] [] [] [] [] [] := by
  have h0 := hw 0; have h1 := hw 1; have h2 := hw 2; have h3 := hw 3; have h4 := hw 4
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> first | rfl | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

private theorem copy_run (old : Fin 44 → List Bool) :
    ∃ used ≤ 2*(old 14).length+2,
      tick^[used] (state (some (copyLabel 0)) old [] [] [] [] [] []) =
        state (some 17) old (old 14) [] [] [] [] [] := by
  let raw := old 14
  let initial := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory (BitCopyMachine.config (some false) raw [] [])
  let final := TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.copyPorts
    PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory (BitCopyMachine.config none raw raw [])
  let frame : Fin 45 → List Bool := fun k =>
    (state (some (copyLabel 0)) old [] [] [] [] [] []).stk (copyLayout (.inr k))
  have hi : (TM2ReturnLink.tick (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
      PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program))^[2*raw.length+2]
      initial = final := by
    dsimp only [initial]
    rw [TM2FiniteCoordinates.run]
    rw [show (TM2ReturnLink.tick BitCopyMachine.program)^[2*raw.length+2]
      (BitCopyMachine.config (some false) raw [] []) =
      BitCopyMachine.config none raw (raw++[]) [] from BitCopyMachine.run raw [] none]
    simp only [List.append_nil]
    rfl
  have hf := TM2StackFrame.run copyLayout
    (TM2FiniteCoordinates.program PrimeNonceCiphertextMachine.copyPorts
      PrimeNonceCiphertextMachine.copyLabels BinaryModuloCode.memory BitCopyMachine.program)
    (2*raw.length+2) initial frame
  rw [hi] at hf
  change (TM2ReturnLink.tick copyProgram)^[2*raw.length+2]
    (TM2StackFrame.embed copyLayout initial frame) = TM2StackFrame.embed copyLayout final frame at hf
  obtain ⟨u,hu,he⟩ := TM2ReturnLink.run copyProgram program copyLabel 17 copy_code
    (2*raw.length+2) _ (by rw [hf]; rfl)
  rw [hf] at he
  have hs : TM2ReturnLink.embed copyLabel 17 (TM2StackFrame.embed copyLayout initial frame) =
      state (some (copyLabel 0)) old [] [] [] [] [] [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  have ht : TM2ReturnLink.embed copyLabel 17 (TM2StackFrame.embed copyLayout final frame) =
      state (some 17) old (old 14) [] [] [] [] [] := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1; funext k; fin_cases k <;> rfl
  exact ⟨u,hu,by rwa [hs,ht] at he⟩

private theorem outer_header (old : Fin 44 → List Bool) (suffix : List Bool) :
    tick^[7] (state (some 17) old (uniformNatEncode 5++suffix) [] [] [] [] []) =
      state (some (fieldLabel 0 0)) old suffix [] [] [] [] [] := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> rfl

private def beforePair (phase : Fin 3) (old : Fin 44 → List Bool)
    (suffix a b shadow live flag history : List Bool) : Config :=
  state (some ⟨24+5*phase.val,by simp only [size]; omega⟩) old
    (if phase = 1 then uniformNatEncode 2++suffix else a)
    (if phase = 1 then b else uniformNatEncode 2++suffix) shadow live flag history
private def afterPair (phase : Fin 3) (old : Fin 44 → List Bool)
    (suffix a b shadow live flag history : List Bool) : Config :=
  state (some (fieldLabel (![5,7,9] phase) 0)) old
    (if phase = 1 then suffix else a) (if phase = 1 then b else suffix) shadow live flag history

private theorem pair_header (phase : Fin 3) (old : Fin 44 → List Bool)
    (suffix a b shadow live flag history : List Bool) :
    tick^[5] (beforePair phase old suffix a b shadow live flag history) =
      afterPair phase old suffix a b shadow live flag history := by
  fin_cases phase
  · have h0 : tick (state (some 24) old a (true :: true :: false :: false :: true :: suffix) shadow live flag history) = state (some 25) old a (true :: false :: false :: true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h1 : tick (state (some 25) old a (true :: false :: false :: true :: suffix) shadow live flag history) = state (some 26) old a (false :: false :: true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h2 : tick (state (some 26) old a (false :: false :: true :: suffix) shadow live flag history) = state (some 27) old a (false :: true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h3 : tick (state (some 27) old a (false :: true :: suffix) shadow live flag history) = state (some 28) old a (true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h4 : tick (state (some 28) old a (true :: suffix) shadow live flag history) = state (some 86) old a (suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    change tick (tick (tick (tick (tick (state (some 24) old a (true :: true :: false :: false :: true :: suffix) shadow live flag history))))) = state (some 86) old a (suffix) shadow live flag history
    rw [h0,h1,h2,h3,h4]
  · have h0 : tick (state (some 29) old (true :: true :: false :: false :: true :: suffix) b shadow live flag history) = state (some 30) old (true :: false :: false :: true :: suffix) b shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h1 : tick (state (some 30) old (true :: false :: false :: true :: suffix) b shadow live flag history) = state (some 31) old (false :: false :: true :: suffix) b shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h2 : tick (state (some 31) old (false :: false :: true :: suffix) b shadow live flag history) = state (some 32) old (false :: true :: suffix) b shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h3 : tick (state (some 32) old (false :: true :: suffix) b shadow live flag history) = state (some 33) old (true :: suffix) b shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h4 : tick (state (some 33) old (true :: suffix) b shadow live flag history) = state (some 104) old (suffix) b shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    change tick (tick (tick (tick (tick (state (some 29) old (true :: true :: false :: false :: true :: suffix) b shadow live flag history))))) = state (some 104) old (suffix) b shadow live flag history
    rw [h0,h1,h2,h3,h4]
  · have h0 : tick (state (some 34) old a (true :: true :: false :: false :: true :: suffix) shadow live flag history) = state (some 35) old a (true :: false :: false :: true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h1 : tick (state (some 35) old a (true :: false :: false :: true :: suffix) shadow live flag history) = state (some 36) old a (false :: false :: true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h2 : tick (state (some 36) old a (false :: false :: true :: suffix) shadow live flag history) = state (some 37) old a (false :: true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h3 : tick (state (some 37) old a (false :: true :: suffix) shadow live flag history) = state (some 38) old a (true :: suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    have h4 : tick (state (some 38) old a (true :: suffix) shadow live flag history) = state (some 122) old a (suffix) shadow live flag history := by
      change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
      congr 1; funext k; fin_cases k <;> rfl
    change tick (tick (tick (tick (tick (state (some 34) old a (true :: true :: false :: false :: true :: suffix) shadow live flag history))))) = state (some 122) old a (suffix) shadow live flag history
    rw [h0,h1,h2,h3,h4]


private def clearLabel (phase : Fin 4) : Fin size := ⟨12+phase.val,by simp only [size]; omega⟩
private def clearNext (phase : Fin 4) : Fin 11 := ⟨phase.val+1,by omega⟩
private theorem clear_step (phase : Fin 4) (old : Fin 44 → List Bool)
    (a payload shadow live flag history : List Bool) (b : Bool) (v : Fin 3) :
    tick (state (some (clearLabel phase)) old a (b::payload) shadow live flag history v) =
      state (some (clearLabel phase)) old a payload shadow live flag history (if b then 2 else 1) := by
  fin_cases phase <;> cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem clear_nil (phase : Fin 4) (old : Fin 44 → List Bool)
    (a shadow live flag history : List Bool) (v : Fin 3) :
    tick (state (some (clearLabel phase)) old a [] shadow live flag history v) =
      state (some (fieldLabel (clearNext phase) 0)) old a [] shadow live flag history := by
  fin_cases phase <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl
private theorem clear_run (phase : Fin 4) (old : Fin 44 → List Bool)
    (a payload shadow live flag history : List Bool) (v : Fin 3) :
    tick^[payload.length+1] (state (some (clearLabel phase)) old a payload shadow live flag history v) =
      state (some (fieldLabel (clearNext phase) 0)) old a [] shadow live flag history := by
  induction payload generalizing v with
  | nil => simpa only [List.length_nil,zero_add,Function.iterate_one] using clear_nil phase old a shadow live flag history v
  | cons b bs ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,clear_step,ih]

private theorem final_flag (old : Fin 44 → List Bool) (shadow live history : List Bool) (bad : Bool) :
    tick (state (some 16) old [] [] shadow live [bad] history) =
      state none old [] [] shadow live [bad] history 2 := by
  cases bad <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; fin_cases k <;> rfl

private theorem final_eq (old : Fin 44 → List Bool) (shadow live flag history : List Bool)
    (hw : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    state none old [] [] shadow live flag history 2 = result old shadow live flag history := by
  have h0 := (hw 0).symm; have h1 := (hw 1).symm; have h2 := (hw 2).symm
  have h3 := (hw 3).symm; have h4 := (hw 4).symm
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1; funext k; fin_cases k <;> first | rfl | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

#print axioms copy_run
#print axioms outer_header
#print axioms pair_header
#print axioms clear_run
#print axioms final_flag
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
/-- Every payload consumed by the eleven existing field-parser calls is bounded
by the actual raw record length; nested state sizes are not supplied premises. -/
theorem payload_lengths (a b c d shadow live flag history : List Bool) :
    let flagHistory := bitFieldsEncode [flag,history]
    let programmed := bitFieldsEncode [shadow,flagHistory]
    let saved := bitFieldsEncode [programmed,live]
    let N := (input a b c d shadow live flag history).length
    ∀ w ∈ [a,b,c,d,saved,programmed,live,shadow,flagHistory,flag,history], w.length ≤ N := by
  dsimp only
  have hflagHistory := bitFieldsEncode_length [flag,history]
  have hprog := bitFieldsEncode_length [shadow,bitFieldsEncode [flag,history]]
  have hsaved := bitFieldsEncode_length
    [bitFieldsEncode [shadow,bitFieldsEncode [flag,history]],live]
  have hraw := bitFieldsEncode_length [a,b,c,d,
    bitFieldsEncode [bitFieldsEncode [shadow,bitFieldsEncode [flag,history]],live]]
  change (input a b c d shadow live flag history).length = _ at hraw
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil] at hflagHistory hprog hsaved hraw
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
open Turing.TM2
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

private theorem fieldClock_mono {m n : Nat} (h : m ≤ n) : fieldClock m ≤ fieldClock n := by
  have hs := Nat.size_le_size h
  have hm := Nat.mul_le_mul h (show 2*m.size+3 ≤ 2*n.size+3 by omega)
  unfold fieldClock
  omega

/-- Complete canonical nested-state extraction, retaining all original words.
The singleton Boolean is checked by executed control, not merely projected. -/
theorem run (a b c d shadow live history : List Bool) (bad : Bool)
    (old : Fin 44 → List Bool)
    (hraw : old 14 = input a b c d shadow live [bad] history)
    (hwork : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    ∃ used ≤ clock (old 14).length,
      tick^[used] (start old) = result old shadow live [bad] history := by
  let flagHistory := bitFieldsEncode [[bad],history]
  let programmed := bitFieldsEncode [shadow,flagHistory]
  let saved := bitFieldsEncode [programmed,live]
  let t4 := framedWord saved []
  let t3 := framedWord d t4
  let t2 := framedWord c t3
  let t1 := framedWord b t2
  let t0 := framedWord a t1
  let N := (input a b c d shadow live [bad] history).length
  have shape : old 14 = uniformNatEncode 5 ++ t0 := by
    rw [hraw]
    simp only [input,t0,t1,t2,t3,t4,saved,programmed,flagHistory,
      bitFieldsEncode,bitFramesEncode,framedWord,List.length_cons,List.length_nil,List.append_nil,List.append_assoc]
  have savedShape : saved = uniformNatEncode 2 ++ framedWord programmed (framedWord live []) := by
    simp [saved,bitFieldsEncode,bitFramesEncode,framedWord,List.append_assoc]
  have programmedShape : programmed = uniformNatEncode 2 ++ framedWord shadow (framedWord flagHistory []) := by
    simp [programmed,bitFieldsEncode,bitFramesEncode,framedWord,List.append_assoc]
  have flagHistoryShape : flagHistory = uniformNatEncode 2 ++ framedWord [bad] (framedWord history []) := by
    simp [flagHistory,bitFieldsEncode,bitFramesEncode,framedWord,List.append_assoc]
  have lens := payload_lengths a b c d shadow live [bad] history
  change ∀ w ∈ [a,b,c,d,saved,programmed,live,shadow,flagHistory,[bad],history], w.length ≤ N at lens
  have lenraw : (old 14).length = N := congrArg List.length hraw
  have en : tick^[1] (start old) = state (some (copyLabel 0)) old [] [] [] [] [] [] := entry old hwork
  obtain ⟨cp,bcp,hcp⟩ := copy_run old
  rw [shape] at hcp
  have ho := outer_header old t0
  obtain ⟨f0,bf0,hf0⟩ := field_run 0 old a t1 [] [] [] [] [] []
  have b0 := bf0.trans (fieldClock_mono (lens a (by simp)))
  have g0 : tick^[1] (afterField 0 old a t1 [] [] [] [] [] []) =
      state (some (clearLabel 0)) old t1 a [] [] [] [] := rfl
  have clear0 := clear_run 0 old t1 a [] [] [] [] 0
  obtain ⟨f1,bf1,hf1⟩ := field_run 1 old b t2 [] [] [] [] [] []
  have b1 := bf1.trans (fieldClock_mono (lens b (by simp)))
  have g1 : tick^[1] (afterField 1 old b t2 [] [] [] [] [] []) =
      state (some (clearLabel 1)) old t2 b [] [] [] [] := rfl
  have clear1 := clear_run 1 old t2 b [] [] [] [] 0
  obtain ⟨f2,bf2,hf2⟩ := field_run 2 old c t3 [] [] [] [] [] []
  have b2 := bf2.trans (fieldClock_mono (lens c (by simp)))
  have g2 : tick^[1] (afterField 2 old c t3 [] [] [] [] [] []) =
      state (some (clearLabel 2)) old t3 c [] [] [] [] := rfl
  have clear2 := clear_run 2 old t3 c [] [] [] [] 0
  obtain ⟨f3,bf3,hf3⟩ := field_run 3 old d t4 [] [] [] [] [] []
  have b3 := bf3.trans (fieldClock_mono (lens d (by simp)))
  have g3 : tick^[1] (afterField 3 old d t4 [] [] [] [] [] []) =
      state (some (clearLabel 3)) old t4 d [] [] [] [] := rfl
  have clear3 := clear_run 3 old t4 d [] [] [] [] 0
  obtain ⟨f4,bf4,hf4⟩ := field_run 4 old saved [] [] [] [] [] [] []
  have b4 := bf4.trans (fieldClock_mono (lens saved (by simp)))
  have g4 : tick^[1] (afterField 4 old saved [] [] [] [] [] [] []) =
      state (some 24) old [] saved [] [] [] [] := rfl
  have hp0 := pair_header 0 old (framedWord programmed (framedWord live [])) [] [] [] [] [] []
  change tick^[5] (state (some 24) old [] (uniformNatEncode 2 ++ framedWord programmed (framedWord live [])) [] [] [] []) = _ at hp0
  rw [←savedShape] at hp0
  obtain ⟨f5,bf5,hf5⟩ := field_run 5 old programmed (framedWord live []) [] [] [] [] [] []
  have b5 := bf5.trans (fieldClock_mono (lens programmed (by simp)))
  have g5 : tick^[1] (afterField 5 old programmed (framedWord live []) [] [] [] [] [] []) =
      state (some (fieldLabel 6 0)) old programmed (framedWord live []) [] [] [] [] := rfl
  obtain ⟨f6,bf6,hf6⟩ := field_run 6 old live [] programmed [] [] [] [] []
  have b6 := bf6.trans (fieldClock_mono (lens live (by simp)))
  have g6 : tick^[1] (afterField 6 old live [] programmed [] [] [] [] []) =
      state (some 29) old programmed [] [] live [] [] := rfl
  have hp1 := pair_header 1 old (framedWord shadow (framedWord flagHistory [])) [] [] [] live [] []
  change tick^[5] (state (some 29) old (uniformNatEncode 2 ++ framedWord shadow (framedWord flagHistory [])) [] [] live [] []) = _ at hp1
  rw [←programmedShape] at hp1
  obtain ⟨f7,bf7,hf7⟩ := field_run 7 old shadow (framedWord flagHistory []) [] [] [] live [] []
  have b7 := bf7.trans (fieldClock_mono (lens shadow (by simp)))
  have g7 : tick^[1] (afterField 7 old shadow (framedWord flagHistory []) [] [] [] live [] []) =
      state (some (fieldLabel 8 0)) old (framedWord flagHistory []) [] shadow live [] [] := rfl
  obtain ⟨f8,bf8,hf8⟩ := field_run 8 old flagHistory [] [] [] shadow live [] []
  have b8 := bf8.trans (fieldClock_mono (lens flagHistory (by simp)))
  have g8 : tick^[1] (afterField 8 old flagHistory [] [] [] shadow live [] []) =
      state (some 34) old [] flagHistory shadow live [] [] := rfl
  have hp2 := pair_header 2 old (framedWord [bad] (framedWord history [])) [] [] shadow live [] []
  change tick^[5] (state (some 34) old [] (uniformNatEncode 2 ++ framedWord [bad] (framedWord history [])) shadow live [] []) = _ at hp2
  rw [←flagHistoryShape] at hp2
  obtain ⟨f9,bf9,hf9⟩ := field_run 9 old [bad] (framedWord history []) [] [] shadow live [] []
  have b9 := bf9.trans (fieldClock_mono (lens [bad] (by simp)))
  have g9 : tick^[1] (afterField 9 old [bad] (framedWord history []) [] [] shadow live [] []) =
      state (some (fieldLabel 10 0)) old [] (framedWord history []) shadow live [bad] [] := rfl
  obtain ⟨f10,bf10,hf10⟩ := field_run 10 old history [] [] [] shadow live [bad] []
  have b10 := bf10.trans (fieldClock_mono (lens history (by simp)))
  have g10 : tick^[1] (afterField 10 old history [] [] [] shadow live [bad] []) =
      state (some 16) old [] [] shadow live [bad] history := rfl
  have hf : tick^[1] (state (some 16) old [] [] shadow live [bad] history) =
      state none old [] [] shadow live [bad] history 2 := final_flag old shadow live history bad
  have chain0 := sequence en hcp
  have chain1 := sequence chain0 ho
  have chain2 := sequence chain1 hf0
  have chain3 := sequence chain2 g0
  have chain4 := sequence chain3 clear0
  have chain5 := sequence chain4 hf1
  have chain6 := sequence chain5 g1
  have chain7 := sequence chain6 clear1
  have chain8 := sequence chain7 hf2
  have chain9 := sequence chain8 g2
  have chain10 := sequence chain9 clear2
  have chain11 := sequence chain10 hf3
  have chain12 := sequence chain11 g3
  have chain13 := sequence chain12 clear3
  have chain14 := sequence chain13 hf4
  have chain15 := sequence chain14 g4
  have chain16 := sequence chain15 hp0
  have chain17 := sequence chain16 hf5
  have chain18 := sequence chain17 g5
  have chain19 := sequence chain18 hf6
  have chain20 := sequence chain19 g6
  have chain21 := sequence chain20 hp1
  have chain22 := sequence chain21 hf7
  have chain23 := sequence chain22 g7
  have chain24 := sequence chain23 hf8
  have chain25 := sequence chain24 g8
  have chain26 := sequence chain25 hp2
  have chain27 := sequence chain26 hf9
  have chain28 := sequence chain27 g9
  have chain29 := sequence chain28 hf10
  have chain30 := sequence chain29 g10
  have chain31 := sequence chain30 hf
  rw [final_eq old shadow live [bad] history hwork] at chain31
  refine ⟨_,?_,chain31⟩
  have la := lens a (by simp)
  have lb := lens b (by simp)
  have lc := lens c (by simp)
  have ld := lens d (by simp)
  rw [lenraw] at bcp ⊢
  unfold clock
  clear en hcp ho hf hp0 hp1 hp2 shape savedShape programmedShape flagHistoryShape lens clear0 clear1 clear2 clear3 hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hf10 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 bf0 bf1 bf2 bf3 bf4 bf5 bf6 bf7 bf8 bf9 bf10 chain0 chain1 chain2 chain3 chain4 chain5 chain6 chain7 chain8 chain9 chain10 chain11 chain12 chain13 chain14 chain15 chain16 chain17 chain18 chain19 chain20 chain21 chain22 chain23 chain24 chain25 chain26 chain27 chain28 chain29 chain30 chain31
  simp only [←Nat.add_assoc]
  omega

/-- Pad only after the exact successful halt of the original controller. -/
theorem padded_run (a b c d shadow live history : List Bool) (bad : Bool)
    (old : Fin 44 → List Bool)
    (hraw : old 14 = input a b c d shadow live [bad] history)
    (hwork : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    tick^[clock (old 14).length] (start old) = result old shadow live [bad] history := by
  obtain ⟨u,hu,he⟩ := run a b c d shadow live history bad old hraw hwork
  rw [show clock (old 14).length = (clock (old 14).length-u)+u by omega,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (show tick (result old shadow live [bad] history) = _ from rfl) _

theorem local_cost (l : Fin size) : BitOracleMachine.localCost (program l) ≤ 32 := by
  fin_cases l <;> decide +kernel

/-- Actual complete execution charge, derived from the original instructions. -/
theorem charged (a b c d shadow live history : List Bool) (bad : Bool)
    (old : Fin 44 → List Bool)
    (hraw : old 14 = input a b c d shadow live [bad] history)
    (hwork : ∀ j : Fin 5, old ⟨23+j.val,by omega⟩ = []) :
    ∃ charge ≤ cost (old 14).length,
      BitOracleMachine.run code (clock (old 14).length) (start old) =
        pure (result old shadow live [bad] history,charge) := by
  obtain ⟨charge,hc,he⟩ := BitOracleMachine.compute_run_cost program 32 local_cost
    (clock (old 14).length) (start old)
  rw [show (TM2ReturnLink.tick program)^[clock (old 14).length] (start old) =
    result old shadow live [bad] history from padded_run a b c d shadow live history bad old hraw hwork] at he
  exact ⟨charge,hc,he⟩

#print axioms run
#print axioms padded_run
#print axioms local_cost
#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine

namespace ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
/-- The actual parser clock is quadratic in its complete raw input length. -/
theorem clock_le_quadratic (N : Nat) : clock N ≤ 22*N*N+72*N+118 := by
  have hs : N.size ≤ N := Nat.size_le.mpr N.lt_two_pow_self
  unfold clock fieldClock
  calc
    _ ≤ 11*(3*N+7+N*(2*N+3))+6*N+41 := by gcongr
    _ = _ := by ring

/-- Derived local bit-action charge; no enclosing-caller efficiency claim. -/
theorem cost_le_quadratic (N : Nat) : cost N ≤ 32*(22*N*N+72*N+118) :=
  Nat.mul_le_mul_left 32 (clock_le_quadratic N)


#print axioms clock_le_quadratic
#print axioms cost_le_quadratic
end ExplainableCrypto.Helios.Computational.PrimeProgrammedStateInputMachine
