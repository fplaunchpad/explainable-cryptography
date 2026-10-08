import ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
import ExplainableCrypto.Helios.Computational.ScalarComplementMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open Turing.TM2

theorem transfer_code (which : Fin 9) (l : Fin 4) :
    program (transferLabel which l) =
      TM2ReturnLink.redirect (transferLabel which) (transferReturn which) (transferProgram which l) := by
  have h0 : ¬ (transferLabel which l).val < 13 := by dsimp [transferLabel]; omega
  have h1 : (transferLabel which l).val < 49 := by
    have := which.isLt; have := l.isLt; dsimp [transferLabel]; omega
  rw [program,dif_neg h0,dif_pos h1]
  have hw : ((transferLabel which l).val-13)/4 = which.val := by
    have := l.isLt; dsimp [transferLabel]; omega
  have hl : ((transferLabel which l).val-13)%4 = l.val := by
    have := l.isLt; dsimp [transferLabel]; omega
  simp only [hw,hl]

theorem parse_code (l : Fin 3) :
    program (parseLabel l) = TM2ReturnLink.redirect parseLabel 2 (parseProgram l) := by
  have h0 : ¬ (parseLabel l).val < 13 := by dsimp [parseLabel]; omega
  have h1 : ¬ (parseLabel l).val < 49 := by dsimp [parseLabel]; omega
  have h2 : (parseLabel l).val < 52 := by have := l.isLt; dsimp [parseLabel]; omega
  rw [program,dif_neg h0,dif_neg h1,dif_pos h2]
  simp only [parseLabel,Nat.add_sub_cancel_left]

theorem power_code (which : Fin 2) (l : Fin 192) :
    program (powerLabel which l) = TM2ReturnLink.redirect (powerLabel which)
      (if which == 0 then 3 else 4) (powerProgram l) := by
  have h0 : ¬ (powerLabel which l).val < 13 := by dsimp [powerLabel]; omega
  have h1 : ¬ (powerLabel which l).val < 49 := by dsimp [powerLabel]; omega
  have h2 : ¬ (powerLabel which l).val < 52 := by dsimp [powerLabel]; omega
  have h3 : (powerLabel which l).val < 436 := by
    have := which.isLt; have := l.isLt; dsimp [powerLabel]; omega
  rw [program,dif_neg h0,dif_neg h1,dif_neg h2,dif_pos h3]
  have hw : ((powerLabel which l).val-52)/192 = which.val := by
    have := l.isLt; dsimp [powerLabel]; omega
  have hl : ((powerLabel which l).val-52)%192 = l.val := by
    have := l.isLt; dsimp [powerLabel]; omega
  simp only [hw,hl]

theorem multiply_code (l : Fin 86) :
    program (multiplyLabel l) = TM2ReturnLink.redirect multiplyLabel 5 (multiplyProgram l) := by
  have h0 : ¬ (multiplyLabel l).val < 13 := by dsimp [multiplyLabel]; omega
  have h1 : ¬ (multiplyLabel l).val < 49 := by dsimp [multiplyLabel]; omega
  have h2 : ¬ (multiplyLabel l).val < 52 := by dsimp [multiplyLabel]; omega
  have h3 : ¬ (multiplyLabel l).val < 436 := by dsimp [multiplyLabel]; omega
  have h4 : (multiplyLabel l).val < 522 := by have := l.isLt; dsimp [multiplyLabel]; omega
  rw [program,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_pos h4]
  simp only [multiplyLabel,Nat.add_sub_cancel_left]

theorem complement_code (l : Fin 21) :
    program (complementLabel l) = TM2ReturnLink.redirect complementLabel 1 (complementProgram l) := by
  have h0 : ¬ (complementLabel l).val < 13 := by dsimp [complementLabel]; omega
  have h1 : ¬ (complementLabel l).val < 49 := by dsimp [complementLabel]; omega
  have h2 : ¬ (complementLabel l).val < 52 := by dsimp [complementLabel]; omega
  have h3 : ¬ (complementLabel l).val < 436 := by dsimp [complementLabel]; omega
  have h4 : ¬ (complementLabel l).val < 522 := by dsimp [complementLabel]; omega
  rw [program,dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h3,dif_neg h4]
  simp only [complementLabel,Nat.add_sub_cancel_left]

/-- Exact finite presentation of a framed transfer, including old destination
and private scratch. Caller equality establishes the required initial shape. -/
def transferState (which : Fin 9) (phase : Option BitPortTransfer.Label)
    (word old scratch : List Bool) (frame : Fin 35 → List Bool) (v : Option Bool := none) :
    BitOracleMachine.Config 38 4 3 :=
  TM2FiniteCoordinates.present (Equiv.refl (Fin 38)) transferLabels BinaryModuloCode.memory
    (TM2StackFrame.embed (transferLayout which) (BitPortTransfer.config phase word old scratch v) frame)

/-- Actual transfer slice returns live, retaining the whole arbitrary frame.
Old destinations are replaced, and exactly the selected slices consume source. -/
theorem transfer_run (which : Fin 9) (word old : List Bool) (frame : Fin 35 → List Bool)
    (v : Option Bool) :
    ∃ used ≤ old.length+(if consumes which then 3 else 2)*word.length+4,
      tick^[used] (TM2ReturnLink.embed (transferLabel which) (transferReturn which)
        (transferState which (some .clear) word old [] frame v)) =
      TM2ReturnLink.embed (transferLabel which) (transferReturn which)
        (transferState which none (if consumes which then [] else word) word [] frame) := by
  have h : ∃ u ≤ old.length+(if consumes which then 3 else 2)*word.length+4,
      (BitPortTransfer.tick (consumes which))^[u] (BitPortTransfer.config (some .clear) word old [] v) =
      BitPortTransfer.config none (if consumes which then [] else word) word [] := by
    cases hm : consumes which
    · simpa only [hm,Bool.false_eq_true,if_false] using BitPortTransfer.run word old v
    · simpa only [hm,if_true] using BitPortTransfer.consume_run word old v
  obtain ⟨u,hu,he⟩ := h
  have hc : (TM2ReturnLink.tick (transferProgram which))^[u]
      (transferState which (some .clear) word old [] frame v) =
      transferState which none (if consumes which then [] else word) word [] frame := by
    unfold transferProgram transferState
    rw [TM2FiniteCoordinates.run,TM2StackFrame.run,he]
  obtain ⟨w,hw,hw'⟩ := TM2ReturnLink.run (transferProgram which) program (transferLabel which)
    (transferReturn which) (transfer_code which) u _ (by rw [hc]; rfl)
  rw [hc] at hw'
  exact ⟨w,hw.trans hu,hw'⟩

/-- Exact parser workspace plus arbitrary untouched caller frame. -/
def parseState (phase : Option NatPrefixMachine.Label)
    (input count scratch output : List Bool) (frame : Fin 34 → List Bool) (v : Option Bool := none) :
    BitOracleMachine.Config 38 3 3 :=
  TM2StackFrame.embed parseLayout
    (TM2FiniteCoordinates.present PrimeNonceCiphertextMachine.parsePorts
      PrimeNonceCiphertextMachine.parseLabels BinaryModuloCode.memory
      (NatPrefixMachine.config phase input count scratch output v)) frame

/-- The actual parser slice consumes one canonical prefix, preserves its suffix
and all frame words, and returns success to the caller's actual guard. -/
theorem parse_run (n : Nat) (suffix : List Bool) (frame : Fin 34 → List Bool) :
    ∃ used ≤ 3*n.size+3,
      tick^[used] (TM2ReturnLink.embed parseLabel 2
        (parseState (some .width) (uniformNatEncode n++suffix) [] [] [] frame)) =
      TM2ReturnLink.embed parseLabel 2 (parseState none suffix [] [] n.bits frame (some true)) := by
  have he := NatPrefixMachine.encoded_run n suffix
  change (TM2ReturnLink.tick NatPrefixMachine.program)^[3*n.size+3]
    (NatPrefixMachine.config (some .width) (uniformNatEncode n++suffix) [] [] []) =
    NatPrefixMachine.config none suffix [] [] n.bits (some true) at he
  have hc : (TM2ReturnLink.tick parseProgram)^[3*n.size+3]
      (parseState (some .width) (uniformNatEncode n++suffix) [] [] [] frame) =
      parseState none suffix [] [] n.bits frame (some true) := by
    unfold parseProgram parseState
    rw [TM2StackFrame.run,TM2FiniteCoordinates.run,he]
  obtain ⟨u,hu,hu'⟩ := TM2ReturnLink.run parseProgram program parseLabel 2 parse_code
    (3*n.size+3) _ (by rw [hc]; rfl)
  rw [hc] at hu'
  exact ⟨u,hu,hu'⟩

#print axioms transfer_run
#print axioms parse_run
#print axioms transfer_code
#print axioms parse_code
#print axioms power_code
#print axioms multiply_code
#print axioms complement_code
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open Turing.TM2

/-- The complement slice executes in the commitment controller and returns to
its real success guard, retaining every arbitrary framed word. -/
theorem complement_run (q e : Nat) (he : e < q) (frame : Fin 30 → List Bool) :
    ∃ used ≤ ScalarComplementMachine.clock q,
      tick^[used] (TM2ReturnLink.embed complementLabel 1
        (TM2StackFrame.embed complementLayout
          (ScalarComplementMachine.start q.bits (uniformNatEncode e)) frame)) =
      TM2ReturnLink.embed complementLabel 1
        (TM2StackFrame.embed complementLayout
          (ScalarComplementMachine.result q.bits (uniformNatEncode e) e.bits (q-e).bits) frame) := by
  have hr := ScalarComplementMachine.padded_run q e he
  change (TM2ReturnLink.tick ScalarComplementMachine.program)^[ScalarComplementMachine.clock q] _ = _ at hr
  have hf := TM2StackFrame.run complementLayout ScalarComplementMachine.program
    (ScalarComplementMachine.clock q) (ScalarComplementMachine.start q.bits (uniformNatEncode e)) frame
  rw [hr] at hf
  change (TM2ReturnLink.tick complementProgram)^[ScalarComplementMachine.clock q]
    (TM2StackFrame.embed complementLayout (ScalarComplementMachine.start q.bits (uniformNatEncode e)) frame) =
    TM2StackFrame.embed complementLayout
      (ScalarComplementMachine.result q.bits (uniformNatEncode e) e.bits (q-e).bits) frame at hf
  obtain ⟨used,hu,he'⟩ := TM2ReturnLink.run complementProgram program complementLabel 1
    complement_code (ScalarComplementMachine.clock q) _ (by rw [hf]; rfl)
  rw [hf] at he'
  exact ⟨used,hu,he'⟩

/-- Either actual power call preserves its full retained input/context and the
arbitrary surrounding frame, returning live to its own controller guard. -/
theorem power_run (which : Fin 2) (p base : Nat) (raw context : List Bool)
    (hp : 2 ≤ p) (hb : base < p) (frame : Fin 23 → List Bool) :
    ∃ used ≤ BinaryModPower.clock p raw.length,
      tick^[used] (TM2ReturnLink.embed (powerLabel which) (if which == 0 then 3 else 4)
        (TM2StackFrame.embed powerLayout (BinaryModPower.start base.bits raw p.bits context) frame)) =
      TM2ReturnLink.embed (powerLabel which) (if which == 0 then 3 else 4)
        (TM2StackFrame.embed powerLayout
          (BinaryModPower.result ((base^bitsValue raw)%p).bits base.bits raw p.bits context) frame) := by
  have hr := BinaryModPower.padded_run p base raw context hp hb
  change (TM2ReturnLink.tick BinaryModPower.program)^[BinaryModPower.clock p raw.length] _ = _ at hr
  have hf := TM2StackFrame.run powerLayout BinaryModPower.program
    (BinaryModPower.clock p raw.length) (BinaryModPower.start base.bits raw p.bits context) frame
  rw [hr] at hf
  change (TM2ReturnLink.tick powerProgram)^[BinaryModPower.clock p raw.length]
    (TM2StackFrame.embed powerLayout (BinaryModPower.start base.bits raw p.bits context) frame) =
    TM2StackFrame.embed powerLayout
      (BinaryModPower.result ((base^bitsValue raw)%p).bits base.bits raw p.bits context) frame at hf
  obtain ⟨used,hu,he⟩ := TM2ReturnLink.run powerProgram program (powerLabel which)
    (if which == 0 then 3 else 4) (power_code which) (BinaryModPower.clock p raw.length) _
    (by rw [hf]; rfl)
  rw [hf] at he
  exact ⟨used,hu,he⟩

/-- The actual multiply call retains its multiplicand/modulus and all outside
words while consuming its multiplier and clearing its internal workspace. -/
theorem multiply_run (p x : Nat) (raw : List Bool) (hx : x < p) (frame : Fin 27 → List Bool) :
    ∃ used ≤ BinaryModMultiply.clock p raw.length,
      tick^[used] (TM2ReturnLink.embed multiplyLabel 5
        (TM2StackFrame.embed multiplyLayout (BinaryModMultiply.start x.bits raw p.bits) frame)) =
      TM2ReturnLink.embed multiplyLabel 5
        (TM2StackFrame.embed multiplyLayout
          (BinaryModMultiply.result ((x*bitsValue raw)%p).bits x.bits p.bits) frame) := by
  have hr := BinaryModMultiply.padded_run p x raw hx
  change (TM2ReturnLink.tick BinaryModMultiply.program)^[BinaryModMultiply.clock p raw.length] _ = _ at hr
  have hf := TM2StackFrame.run multiplyLayout BinaryModMultiply.program
    (BinaryModMultiply.clock p raw.length) (BinaryModMultiply.start x.bits raw p.bits) frame
  rw [hr] at hf
  change (TM2ReturnLink.tick multiplyProgram)^[BinaryModMultiply.clock p raw.length]
    (TM2StackFrame.embed multiplyLayout (BinaryModMultiply.start x.bits raw p.bits) frame) =
    TM2StackFrame.embed multiplyLayout
      (BinaryModMultiply.result ((x*bitsValue raw)%p).bits x.bits p.bits) frame at hf
  obtain ⟨used,hu,he⟩ := TM2ReturnLink.run multiplyProgram program multiplyLabel 5
    multiply_code (BinaryModMultiply.clock p raw.length) _ (by rw [hf]; rfl)
  rw [hf] at he
  exact ⟨used,hu,he⟩

#print axioms complement_run
#print axioms power_run
#print axioms multiply_run
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
open Turing.TM2

/-- Actual source/destination coordinates of this controller's transfer slices. -/
def transferSource (which : Fin 9) : Fin 38 := transferLayout which (.inl .source)
def transferDestination (which : Fin 9) : Fin 38 := transferLayout which (.inl .destination)
private def transferFrame (which : Fin 9) (words : Fin 38 → List Bool) : Fin 35 → List Bool :=
  fun k => words (transferLayout which (.inr k))

private theorem transfer_scratch (which : Fin 9) :
    transferLayout which (.inl .scratch) = 26 := by fin_cases which <;> rfl

/-- The words view exposes the actual replaced destination and consumed source. -/
def transferWords (which : Fin 9) (words : Fin 38 → List Bool) : Fin 38 → List Bool :=
  Function.update (if consumes which then Function.update words (transferSource which) [] else words)
    (transferDestination which) (words (transferSource which))

private theorem transfer_initial_words (which : Fin 9) (words : Fin 38 → List Bool) (hs : words 26 = []) :
    TM2ReturnLink.embed (transferLabel which) (transferReturn which)
      (transferState which (some .clear) (words (transferSource which))
        (words (transferDestination which)) [] (transferFrame which words) none) =
      (⟨some (transferLabel which 0),0,words⟩ : Config) := by
  have hs' : words (transferLayout which (.inl .scratch)) = [] := by
    rw [transfer_scratch]
    exact hs
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  obtain ⟨j,rfl⟩ := (transferLayout which).surjective k
  cases j with
  | inl j =>
    cases j <;> simp [transferState,TM2FiniteCoordinates.present,TM2FiniteCoordinates.data,
      TM2StackFrame.embed,TM2StackFrame.data,BitPortTransfer.config,BitCopyMachine.config,
      transferSource,transferDestination,hs']
  | inr j =>
    simp [transferState,TM2FiniteCoordinates.present,TM2FiniteCoordinates.data,
      TM2StackFrame.embed,TM2StackFrame.data,transferFrame]

private theorem transfer_final_words (which : Fin 9) (words : Fin 38 → List Bool) (hs : words 26 = []) :
    TM2ReturnLink.embed (transferLabel which) (transferReturn which)
      (transferState which none (if consumes which then [] else words (transferSource which))
        (words (transferSource which)) [] (transferFrame which words)) =
      (⟨some (transferReturn which),0,transferWords which words⟩ : Config) := by
  have hs' : words (transferLayout which (.inl .scratch)) = [] := by
    rw [transfer_scratch]
    exact hs
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  obtain ⟨j,rfl⟩ := (transferLayout which).surjective k
  cases j with
  | inl j =>
    cases j <;> cases hm : consumes which <;>
      simp [transferState,TM2FiniteCoordinates.present,TM2FiniteCoordinates.data,
        TM2StackFrame.embed,TM2StackFrame.data,BitPortTransfer.config,BitCopyMachine.config,
        transferWords,transferSource,transferDestination,Function.update,
        (transferLayout which).injective.eq_iff,hm,hs']
  | inr j =>
    cases hm : consumes which <;>
      simp [transferState,TM2FiniteCoordinates.present,TM2FiniteCoordinates.data,
        TM2StackFrame.embed,TM2StackFrame.data,transferFrame,transferWords,
        transferSource,transferDestination,Function.update,(transferLayout which).injective.eq_iff,hm]

/-- The actual transfer slice in ordinary caller words. Its workspace premise
is discharged by each reached-state presentation in the enclosing proof. -/
theorem transfer_slice (which : Fin 9) (words : Fin 38 → List Bool) (hs : words 26 = []) :
    ∃ used ≤ (words (transferDestination which)).length +
        (if consumes which then 3 else 2)*(words (transferSource which)).length+4,
      tick^[used] (⟨some (transferLabel which 0),0,words⟩ : Config) =
        ⟨some (transferReturn which),0,transferWords which words⟩ := by
  obtain ⟨u,hu,he⟩ := transfer_run which (words (transferSource which))
    (words (transferDestination which)) (transferFrame which words) none
  rw [transfer_initial_words which words hs,transfer_final_words which words hs] at he
  exact ⟨u,hu,he⟩

private def parseFrame (words : Fin 38 → List Bool) : Fin 34 → List Bool :=
  fun k => words (parseLayout (.inr k))

private theorem parse_initial_words (n : Nat) (suffix : List Bool) (words : Fin 38 → List Bool)
    (hi : words 30 = uniformNatEncode n++suffix) (hc : words 24 = [])
    (hs : words 25 = []) (ho : words 36 = []) :
    TM2ReturnLink.embed parseLabel 2
      (parseState (some .width) (uniformNatEncode n++suffix) [] [] [] (parseFrame words)) =
      (⟨some (parseLabel 0),0,words⟩ : Config) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  obtain ⟨j,rfl⟩ := parseLayout.surjective k
  cases j with
  | inl j =>
    simp only [parseState,TM2StackFrame.embed,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
    fin_cases j
    · change uniformNatEncode n++suffix = words 30
      exact hi.symm
    · change [] = words 24
      exact hc.symm
    · change [] = words 25
      exact hs.symm
    · change [] = words 36
      exact ho.symm
  | inr j =>
    simp [parseState,TM2StackFrame.embed,TM2StackFrame.data,parseFrame]

private theorem parse_final_words (n : Nat) (suffix : List Bool) (words : Fin 38 → List Bool)
    (hc : words 24 = []) (hs : words 25 = []) :
    TM2ReturnLink.embed parseLabel 2
      (parseState none suffix [] [] n.bits (parseFrame words) (some true)) =
      (⟨some 2,2,Function.update (Function.update words 30 suffix) 36 n.bits⟩ : Config) := by
  change (⟨_,_,_⟩ : Config) = ⟨_,_,_⟩
  congr 1
  funext k
  obtain ⟨j,rfl⟩ := parseLayout.surjective k
  cases j with
  | inl j =>
    simp only [parseState,TM2StackFrame.embed,TM2StackFrame.data,Equiv.symm_apply_apply,Sum.elim_inl]
    fin_cases j
    · change suffix = (Function.update (Function.update words 30 suffix) 36 n.bits) 30
      simp
    · change [] = (Function.update (Function.update words 30 suffix) 36 n.bits) 24
      simpa using hc.symm
    · change [] = (Function.update (Function.update words 30 suffix) 36 n.bits) 25
      simpa using hs.symm
    · change n.bits = (Function.update (Function.update words 30 suffix) 36 n.bits) 36
      simp
  | inr j =>
    have h30 : parseLayout (.inr j) ≠ 30 := by
      change parseLayout (.inr j) ≠ parseLayout (.inl 0)
      simp
    have h36 : parseLayout (.inr j) ≠ 36 := by
      change parseLayout (.inr j) ≠ parseLayout (.inl 3)
      simp
    simp [parseState,TM2StackFrame.embed,TM2StackFrame.data,parseFrame,
      Function.update,h30,h36]

/-- Actual parser run in ordinary caller words, including retained suffix.
The root's reached phases establish the four input/workspace facts. -/
theorem parser_slice (n : Nat) (suffix : List Bool) (words : Fin 38 → List Bool)
    (hi : words 30 = uniformNatEncode n++suffix) (hc : words 24 = [])
    (hs : words 25 = []) (ho : words 36 = []) :
    ∃ used ≤ 3*n.size+3,
      tick^[used] (⟨some (parseLabel 0),0,words⟩ : Config) =
        ⟨some 2,2,Function.update (Function.update words 30 suffix) 36 n.bits⟩ := by
  obtain ⟨u,hu,he⟩ := parse_run n suffix (parseFrame words)
  rw [parse_initial_words n suffix words hi hc hs ho,parse_final_words n suffix words hc hs] at he
  exact ⟨u,hu,he⟩

#print axioms parser_slice
#print axioms transfer_slice
end ExplainableCrypto.Helios.Computational.PrimeSimCommitMachine
