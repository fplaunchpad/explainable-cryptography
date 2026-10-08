import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded

/-! A physical startup prelude for one raw encoded input word. It writes the
bottom marker, reuses the existing input loader, then enters the primitive loop.
No source configuration is decoded or packed during execution. -/
namespace ExplainableCrypto.Helios.Computational.BitOracleInitialInput
open Turing OracleComp OracleSpec BitOraclePortTransfer TM2TapeRuns
open OracleTapeOutput (wordTape WorkTape)

/-- Source boundary for a raw serialized input; parsing runs in source code. -/
def source {s l m : Nat} (port : Fin s) (label : Option (Fin l))
    (memory : Fin m) (word : List Bool) : BitOracleMachine.Config s l m :=
  ⟨label, memory, Function.update (fun _ => []) port word⟩

inductive State (s l m : Nat) where
  | boot (work : WorkTape (Ports s)) (input : Tape (Option Bool))
  | loading (cfg : OracleTapeInput.Config (Ports s))
  | running (cfg : BitOraclePrimitiveLoop.State s l m)

/-- Input lives on a conventional input tape; working storage starts blank. -/
def initial {s l m : Nat} (word : List Bool) : State s l m :=
  .boot default (wordTape word)

/-- All startup transitions inspect finite phases/current cells and move or
write at most one cell on each tape. Query storage starts blank at handoff. -/
def step {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (port : Fin s) (label : Option (Fin l)) (memory : Fin m) :
    State s l m → OracleComp BitOracleMachine.spec (State s l m)
  | .boot work input => pure (.loading ⟨.seekWork,
      Tape.write (Γ := TM2to1.Γ' (Ports s) (fun _ => Bool)) (true, fun _ => none) work, input⟩)
  | .loading cfg => if cfg.phase = .done then
      pure (.running (.ready label memory ⟨cfg.work, wordTape [], cfg.answer⟩))
    else pure (.loading (OracleTapeInput.step (.inl port) cfg))
  | .running cfg => State.running <$> BitOraclePrimitiveLoop.step code cfg

def run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (port : Fin s) (label : Option (Fin l)) (memory : Fin m) :
    Nat → State s l m → OracleComp BitOracleMachine.spec (State s l m)
  | 0, cfg => pure cfg
  | n + 1, cfg => do
      let next ← step code port label memory cfg
      run code port label memory n next

theorem run_add {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (port : Fin s) (label : Option (Fin l)) (memory : Fin m)
    (a b : Nat) (cfg : State s l m) :
    run code port label memory (a + b) cfg =
      (run code port label memory a cfg >>= run code port label memory b) := by
  induction a generalizing cfg with
  | zero => simp [run]
  | succ a ih => simp [Nat.succ_add, run, ih, bind_assoc]

private theorem blank_packed {K L V : Type} [DecidableEq K] [Fintype K]
    (label : Option L) (memory : V) :
    Tape.write (Γ := TM2to1.Γ' K (fun _ => Bool)) (true, fun _ => none) default =
      (pack (⟨label, memory, fun _ => []⟩ : TM2.Cfg (fun _ : K => Bool) L V)).Tape := by
  have hz : Finset.univ.sup (fun _ : K => (0 : Nat)) = 0 :=
    Nat.eq_zero_of_le_zero Finset.sup_const_le
  simp [pack, columns, height, hz, TM2to1.addBottom]
  rfl

private theorem framed_source {s l m : Nat} (port : Fin s) (label : Option (Fin l))
    (memory : Fin m) (word : List Bool) :
    (BitOracleTapeCompute.framed (source port label memory word)).stk =
      Function.update (fun _ => []) (.inl port) word := by
  funext k
  cases k <;> simp [BitOracleTapeCompute.framed, TM2StackFrame.embed, TM2StackFrame.data, source, Function.update]

/-- Derive a physical handoff from the existing loader's full-tape theorem.
Early completion, if any, ends the prelude; it never pads a live source run. -/
private theorem loading_run {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (port : Fin s) (label : Option (Fin l)) (memory : Fin m)
    (n : Nat) (cfg : OracleTapeInput.Config (Ports s))
    (h : ((OracleTapeInput.step (.inl port))^[n] cfg).phase = .done) :
    ∃ used ≤ n + 1, run code port label memory used (.loading cfg) =
      pure (.running (.ready label memory
        ⟨((OracleTapeInput.step (.inl port))^[n] cfg).work, wordTape [],
          ((OracleTapeInput.step (.inl port))^[n] cfg).answer⟩)) := by
  by_cases hd : cfg.phase = .done
  · have hf : OracleTapeInput.step (.inl port) cfg = cfg := by simp [OracleTapeInput.step, hd]
    rw [Function.iterate_fixed hf]
    exact ⟨1, by omega, by simp [run, step, hd]⟩
  · cases n with
    | zero => exact (hd h).elim
    | succ n =>
      rw [Function.iterate_succ_apply] at h ⊢
      obtain ⟨used, hu, he⟩ := loading_run code port label memory n _ h
      refine ⟨used + 1, by omega, ?_⟩
      simpa only [run, step, hd, ↓reduceIte, pure_bind] using he

/-- Actual blank-tape startup derives the complete canonical ready state,
including both empty private columns, restored input and blank query tape. -/
theorem load {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (port : Fin s) (label : Option (Fin l)) (memory : Fin m) (word : List Bool) :
    ∃ used ≤ 4 * word.length + 8,
      run code port label memory used (initial word) =
        pure (.running (BitOraclePrimitiveLoop.lower code
          (BitOracleTapeLoop.ready (source port label memory word) (wordTape []) (wordTape word)))) := by
  let empty : TM2.Cfg (fun _ : Ports s => Bool) (Fin l) (Fin m) :=
    ⟨label, memory, fun _ => []⟩
  have he := OracleTapeInput.run_packed empty (.inl port) word
  simp only [empty, List.length_nil, Nat.mul_zero, Nat.zero_add] at he
  obtain ⟨used, hu, hr⟩ := loading_run code port label memory (4 * word.length + 6)
    ⟨.seekWork, (pack empty).Tape, wordTape word⟩ (by rw [he])
  rw [he] at hr
  refine ⟨used + 1, by omega, ?_⟩
  simp only [run, initial, step, pure_bind, blank_packed (L := Fin l) label memory]
  rw [hr]
  congr 1
  change State.running (.ready label memory
    ⟨(pack {empty with stk := Function.update (fun _ => []) (.inl port) word}).Tape, wordTape [], wordTape word⟩) =
      State.running (.ready label memory
        ⟨(pack (BitOracleTapeCompute.framed (source port label memory word))).Tape, wordTape [], wordTape word⟩)
  simp only [pack, framed_source]

/-- Once startup returns, the original primitive loop runs unchanged. -/
theorem run_running {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (port : Fin s) (label : Option (Fin l)) (memory : Fin m)
    (fuel : Nat) (cfg : BitOraclePrimitiveLoop.State s l m) :
    run code port label memory fuel (.running cfg) =
      State.running <$> BitOraclePrimitiveLoop.run code fuel cfg := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih => simp only [run, step, BitOraclePrimitiveLoop.run, bind_map_left, ih, map_bind]

/-- Interpret complete caller state only at a primitive ready boundary. -/
def observe {s l m : Nat} : State s l m → Option (BitOracleMachine.Config s l m)
  | .running cfg => BitOraclePrimitiveBounded.observe cfg
  | _ => none

/-- Startup chooses no oracle answers. Its derived length is shared by the
whole source query tree, and adds at most a linear input-loading overhead. -/
theorem run_source_bounded {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (port : Fin s) (label : Option (Fin l)) (memory : Fin m) (word : List Bool)
    (sourceFuel limit bound : Nat)
    (h : BitOracleLoopBounded.Within limit bound
      (BitOracleMachine.run code sourceFuel (source port label memory word))) :
    let clock := BitOracleTapeCap.unitCost
      (height (source port label memory word).stk + bound + 0) * bound *
        BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4 * word.length + 8,
      observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (run code port label memory (startup + clock) (initial word)) =
      (fun out => some out.1) <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleMachine.run code sourceFuel (source port label memory word)) := by
  obtain ⟨startup, hs, he⟩ := load code port label memory word
  refine ⟨startup, hs, ?_⟩
  rw [run_add, he, pure_bind, run_running, simulateQ_map, Functor.map_map]
  exact BitOraclePrimitiveBounded.run_source_bounded code sourceFuel limit bound
    (source port label memory word) [] (wordTape word) h

/-- The same input-loading clock transports every lawful bounded handler,
including all of a stateful probabilistic handler's effects. -/
theorem run_source_handler {s l m : Nat} {M : Type → Type} [Monad M] [LawfulMonad M]
    (code : BitOracleMachine.Code s l m) (port : Fin s) (label : Option (Fin l))
    (memory : Fin m) (word : List Bool) (sourceFuel limit bound : Nat)
    (h : BitOracleLoopBounded.Within limit bound
      (BitOracleMachine.run code sourceFuel (source port label memory word)))
    (handler : QueryImpl (BitOracleLoopBounded.spec limit) M) :
    let clock := BitOracleTapeCap.unitCost
      (height (source port label memory word).stk + bound + 0) * bound *
        BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4 * word.length + 8,
      observe <$> simulateQ handler (simulateQ (BitOracleLoopBounded.adapter limit)
        (run code port label memory (startup + clock) (initial word))) =
      (fun out => some out.1) <$> simulateQ handler (simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleMachine.run code sourceFuel (source port label memory word))) := by
  obtain ⟨startup, hs, he⟩ := run_source_bounded code port label memory word sourceFuel limit bound h
  exact ⟨startup, hs, by simpa only [simulateQ_map] using congrArg (simulateQ handler) he⟩

end ExplainableCrypto.Helios.Computational.BitOracleInitialInput
