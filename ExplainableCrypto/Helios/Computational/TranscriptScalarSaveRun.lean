import ExplainableCrypto.Helios.Computational.TranscriptScalarSave

namespace ExplainableCrypto.Helios.Computational.TranscriptScalarSave
open Turing.TM2
set_option maxRecDepth 8192
private abbrev tick (j : Fin 3) := TM2ReturnLink.tick (program j)
private def clearState (j : Fin 3) (phase : Option (Fin 7)) (v : Fin 3)
    (word rest : List Bool) (frame : Fin 20 → List Bool) : Config :=
  ⟨phase,v,Function.update (transferState j (some .clear) word [] frame).stk 2 rest⟩

private theorem clear_step (j : Fin 3) (word rest : List Bool) (frame : Fin 20 → List Bool)
    (v : Fin 3) (b : Bool) :
    tick j (clearState j (some 1) v word (b::rest) frame) =
      clearState j (some 1) (CoinWordLoader.encode (some b)) word rest frame := by
  cases b <;> change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  all_goals congr 1; funext k; by_cases h : k = 2
  all_goals simp [Function.update,h]

private theorem clear_done (j : Fin 3) (word : List Bool) (frame : Fin 20 → List Bool)
    (v : Fin 3) :
    tick j (clearState j (some 1) v word [] frame) =
      TM2ReturnLink.embed transferLabel 6
        (transferState j (some .clear) word [] (Function.update frame 1 [])) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  fin_cases j <;> fin_cases k <;> rfl

private theorem clear_run (j : Fin 3) (word rest : List Bool) (frame : Fin 20 → List Bool)
    (v : Fin 3) :
    (tick j)^[rest.length+1] (clearState j (some 1) v word rest frame) =
      TM2ReturnLink.embed transferLabel 6
        (transferState j (some .clear) word [] (Function.update frame 1 [])) := by
  induction rest generalizing v with
  | nil => simpa using clear_done j word frame v
  | cons b rest ih =>
    rw [List.length_cons,Nat.add_assoc,Function.iterate_succ_apply,clear_step,ih]

private theorem transfer_code (j : Fin 3) (l : Fin 4) :
    program j (transferLabel l) = TM2ReturnLink.redirect transferLabel 6 (transferProgram j l) := by
  fin_cases j <;> fin_cases l <;> rfl

private theorem transfer_run (j : Fin 3) (word : List Bool) (frame : Fin 20 → List Bool) :
    ∃ used ≤ 3*word.length+4,
      (tick j)^[used]
        (TM2ReturnLink.embed transferLabel 6 (transferState j (some .clear) word [] frame)) =
      TM2ReturnLink.embed transferLabel 6 (transferState j none [] word frame) := by
  obtain ⟨u,hu,he⟩ := BitPortTransfer.consume_run word [] none
  have hc : (TM2ReturnLink.tick (transferProgram j))^[u]
      (transferState j (some .clear) word [] frame) = transferState j none [] word frame := by
    unfold transferProgram transferState
    rw [TM2FiniteCoordinates.run,TM2StackFrame.run,he]
  obtain ⟨v,hv,hv'⟩ := TM2ReturnLink.run (transferProgram j) (program j) transferLabel 6
    (transfer_code j) u _ (by rw [hc]; rfl)
  rw [hc] at hv'
  exact ⟨v,by simpa using hv.trans hu,hv'⟩
/-- Execute guard, modulus clearing, consumed scalar transfer and success reset. -/
theorem run (j : Fin 3) (word modulus : List Bool) (frame : Fin 20 → List Bool) :
    ∃ used ≤ clock word modulus,
      (tick j)^[used] (start j word modulus frame) = result j word frame := by
  obtain ⟨u,hu,he⟩ := transfer_run j word (Function.update frame 1 [])
  have hs : tick j (start j word modulus frame) =
      clearState j (some 1) 2 word modulus frame := rfl
  have hf : tick j (TM2ReturnLink.embed transferLabel 6
      (transferState j none [] word (Function.update frame 1 []))) = result j word frame := by
    change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
    congr 1
    funext k
    fin_cases j <;> fin_cases k <;> rfl
  refine ⟨1+(u+(modulus.length+1))+1,by unfold clock; omega,?_⟩
  rw [Function.iterate_succ_apply,hs,
    Function.iterate_add_apply (tick j) 1 (u+(modulus.length+1)),Function.iterate_one,
    Function.iterate_add_apply,clear_run,he,hf]

/-- Repeated simulator draws use a common derived scalar-prefix width. -/
theorem padded_run_bounded (j : Fin 3) (word modulus : List Bool) (frame : Fin 20 → List Bool)
    (bound : Nat) (hb : word.length ≤ bound) :
    (tick j)^[clock (List.replicate bound false) modulus] (start j word modulus frame) =
      result j word frame := by
  obtain ⟨u,hu,he⟩ := run j word modulus frame
  have h : u ≤ clock (List.replicate bound false) modulus := by
    simp only [clock,List.length_replicate] at *
    omega
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le h
  rw [hd,Nat.add_comm u d,Function.iterate_add_apply,he]
  exact Function.iterate_fixed (by rfl) d

theorem local_cost (j : Fin 3) (l : Fin 7) : BitOracleMachine.localCost (program j l) ≤ 5 := by
  fin_cases j <;> fin_cases l <;> decide +kernel

/-- The save's charge follows from its actual consumed-transfer execution. -/
theorem charged_bounded (j : Fin 3) (word modulus : List Bool) (frame : Fin 20 → List Bool)
    (bound : Nat) (hb : word.length ≤ bound) :
    ∃ charge ≤ cost (List.replicate bound false) modulus,
      BitOracleMachine.run (code j) (clock (List.replicate bound false) modulus)
        (start j word modulus frame) = pure (result j word frame,charge) := by
  obtain ⟨c,hc,he⟩ := BitOracleMachine.compute_run_cost (program j) 5 (local_cost j)
    (clock (List.replicate bound false) modulus) (start j word modulus frame)
  refine ⟨c,hc,?_⟩
  change BitOracleMachine.run (code j) (clock (List.replicate bound false) modulus)
    (start j word modulus frame) =
    pure ((tick j)^[clock (List.replicate bound false) modulus] (start j word modulus frame),c) at he
  rw [he,padded_run_bounded j word modulus frame bound hb]

#print axioms run
#print axioms padded_run_bounded
#print axioms local_cost
#print axioms charged_bounded
end ExplainableCrypto.Helios.Computational.TranscriptScalarSave
