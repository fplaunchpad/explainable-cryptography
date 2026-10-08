import ExplainableCrypto.Helios.Computational.CoinModuloMachine
import ExplainableCrypto.Helios.Computational.FrameWriteMachine

/-! The existing scalar writer consumes the sampler's remainder port directly.
Finite renaming and stack framing reuse the original writer proof. This module
checks a two-phase driver; an uninterrupted caller program remains separate. -/
namespace ExplainableCrypto.Helios.Computational.ScalarWriteCode
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
abbrev Config := BitOracleMachine.Config 8 8 3

private def layout : FrameWriteMachine.Stack ⊕ Fin 3 ≃ Fin 8 where
  toFun
    | .inl (.inl .input) => 4 | .inl (.inl .count) => 2
    | .inl (.inl .scratch) => 3 | .inl (.inl .output) => 5
    | .inl (.inr _) => 0 | .inr k => ![1,6,7] k
  invFun := ![.inl (.inr ()),.inr 0,.inl (.inl .count),.inl (.inl .scratch),
    .inl (.inl .input),.inl (.inl .output),.inr 1,.inr 2]
  left_inv k := by
    cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k; rfl
    | inr k => fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

private def labels : FrameWriteMachine.Label ≃ Fin 8 where
  toFun
    | .increment false => 0 | .increment true => 1 | .resume => 2
    | .collect => 3 | .restore => 4 | .digits => 5 | .putbits => 6 | .width => 7
  invFun := ![.increment false,.increment true,.resume,.collect,.restore,.digits,.putbits,.width]
  left_inv l := by cases l <;> first | rfl | (rename_i b; cases b <;> rfl)
  right_inv l := by fin_cases l <;> rfl

private def relocated (l : FrameWriteMachine.Label) :=
  TM2StackFrame.relocate layout (FrameWriteMachine.program l)

def program : Fin 8 → Stmt (fun _ : Fin 8 => Bool) (Fin 8) (Fin 3) :=
  TM2FiniteCoordinates.program (Equiv.refl _) labels BinaryModuloCode.memory relocated

private def present (cfg : FrameWriteMachine.Config) (frame : Fin 3 → List Bool) : Config :=
  TM2FiniteCoordinates.present (Equiv.refl _) labels BinaryModuloCode.memory
    (TM2StackFrame.embed layout cfg frame)

private theorem translated_run (fuel : Nat) (cfg : FrameWriteMachine.Config)
    (frame : Fin 3 → List Bool) :
    (TM2ReturnLink.tick program)^[fuel] (present cfg frame) =
      present (FrameWriteMachine.tick^[fuel] cfg) frame := by
  rw [program,present,TM2FiniteCoordinates.run]
  unfold relocated
  rw [TM2StackFrame.run]
  rfl

def start (digits modulus suffix extra₆ extra₇ : List Bool) : Config :=
  ⟨some 5,0,![digits,modulus,[],[],[],suffix,extra₆,extra₇]⟩

def result (word modulus extra₆ extra₇ : List Bool) : Config :=
  ⟨none,2,![[],modulus,[],[],[],word,extra₆,extra₇]⟩

private theorem present_start (digits modulus suffix extra₆ extra₇ : List Bool) :
    present (FrameWriteMachine.state (some .digits) [] [] [] suffix digits none)
      ![modulus,extra₆,extra₇] = start digits modulus suffix extra₆ extra₇ := by
  apply congrArg (Cfg.mk (some 5) 0)
  funext k; fin_cases k <;> rfl

private theorem present_result (word modulus extra₆ extra₇ : List Bool) :
    present (FrameWriteMachine.state none [] [] [] word [] (some true))
      ![modulus,extra₆,extra₇] = result word modulus extra₆ extra₇ := by
  apply congrArg (Cfg.mk none 2)
  funext k; fin_cases k <;> rfl

/-- Exact writer steps, including the zero delimiter, retain all frame ports. -/
theorem run_digits (n : Nat) (modulus suffix extra₆ extra₇ : List Bool) :
    (TM2ReturnLink.tick program)^[3*n.size+3] (start n.bits modulus suffix extra₆ extra₇) =
      result (uniformNatEncode n++suffix) modulus extra₆ extra₇ := by
  rw [← present_start,translated_run,FrameWriteMachine.prefix_run,present_result]

/-- A constant bound covers the actual translated statements, including entry paths. -/
theorem local_cost (label : Fin 8) : localCost (program label) ≤ 32 := by
  fin_cases label <;> decide +kernel

/-- Resumption changes only finite control. Every sampler stack is passed unchanged. -/
def resumeSampler (cfg : CoinModuloMachine.Config) : Config :=
  ⟨some 5,cfg.var,cfg.stk⟩

/-- The previously executed remainder is serialized without host arithmetic or
loading a newly computed word. Fuel and complete local charge are bounded. -/
theorem from_sampler (bits : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ charge ≤ 32*(3*(q-1).size+3),
      run (fun l => .compute (program l)) (3*(q-1).size+3)
        (resumeSampler (CoinModuloMachine.result (bitsValue bits % q).bits q.bits)) =
      pure (result (uniformNatEncode (bitsValue bits % q)) q.bits [] [],charge) := by
  let n := bitsValue bits % q
  have hn : n ≤ q-1 := Nat.le_sub_one_of_lt (Nat.mod_lt _ hq)
  have hs := Nat.size_le_size hn
  have hb : 3*n.size+3 ≤ 3*(q-1).size+3 := by omega
  obtain ⟨charge,hc,he⟩ := compute_run_cost program 32 local_cost
    (3*(q-1).size+3) (start n.bits q.bits [] [] [])
  refine ⟨charge,hc,?_⟩
  change run _ _ (start n.bits q.bits [] [] []) = _
  rw [he]
  have ht : 3*(q-1).size+3 = (3*(q-1).size+3-(3*n.size+3))+(3*n.size+3) := by omega
  rw [ht,Function.iterate_add_apply,run_digits]
  rw [Function.iterate_fixed (show TM2ReturnLink.tick program
    (result (uniformNatEncode n++[]) q.bits [] []) =
      result (uniformNatEncode n++[]) q.bits [] [] from rfl)]
  simp only [List.append_nil]
  rfl

/-- Two-phase execution passes the complete machine state across a finite-control
resumption boundary. The driver has not yet been compiled into one fixed program. -/
def sampleWord (width : List Bool) (q : Nat) : OracleComp spec (Config × Nat) := do
  let sampled ← run CoinModuloMachine.code (CoinModuloMachine.clock width.length q)
    (CoinModuloMachine.loading (some 15) width [] [] [] q.bits)
  let written ← run (fun l => .compute (program l)) (3*(q-1).size+3)
    (resumeSampler sampled.1)
  pure (written.1,sampled.2+written.2)

/-- The actual two-phase query tree returns the existing scalar prefix and retains
its modulus; no typed scalar value or serialization correspondence is assumed. -/
theorem sampleWord_source (width : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = width.length → charge bits ≤
        CoinModuloMachine.cost width.length q + 32*(3*(q-1).size+3)) ∧
      sampleWord width q =
        (fun bits => (result (uniformNatEncode (bitsValue bits % q)) q.bits [] [],charge bits)) <$>
          CoinWordLoader.word width.length := by
  obtain ⟨sampled,hs,he⟩ := CoinModuloMachine.run_source width q hq
  choose written hw hr using fun bits => from_sampler bits q hq
  refine ⟨fun bits => sampled bits+written bits,?_,?_⟩
  · intro bits hb
    exact Nat.add_le_add (hs bits hb) (hw bits)
  · simp only [sampleWord,he,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    apply bind_congr
    intro bits
    rw [hr]
    simp

/-- Serialized output agrees with the existing finite scalar sampler before any
probability handler is chosen. This is an encoding observation of actual steps. -/
theorem sampleWord_value (q : Nat) [NeZero q] (width : List Bool) :
    (fun out => out.1.stk 5) <$> sampleWord width q =
      simulateQ CoinWordLoader.liftCoins
        ((fun a => uniformNatEncode a.val) <$> sampleFairBitModulo q width.length) := by
  obtain ⟨charge,_,he⟩ := sampleWord_source width q (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [he]
  have h := congrArg (fun computation : OracleComp spec Nat =>
    (fun n => uniformNatEncode (n % q)) <$> computation) (CoinWordLoader.word_index width.length)
  simpa [sampleFairBitModulo,simulateQ_map,Functor.map_map,result] using h

end ExplainableCrypto.Helios.Computational.ScalarWriteCode
