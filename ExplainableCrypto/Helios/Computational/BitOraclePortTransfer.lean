import ExplainableCrypto.Helios.Computational.BitPortTransfer

/-! Actual TM2 response loading for the finite-control oracle interface.
The oracle supplies its word on a private input port. A derived layout places
the caller's destination and other stacks under the existing transfer proof. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePortTransfer
open Turing.TM2 OracleComp OracleSpec
open BitCopyMachine.Stack
abbrev Ports (s : Nat) := Fin s ⊕ Bool

/-- The two additional ports hold the incoming answer and empty scratch. -/
def layout {s : Nat} (destination : Fin s) :
    BitCopyMachine.Stack ⊕ {i : Fin s // i ≠ destination} ≃ Ports s where
  toFun
    | .inl .source => .inr false
    | .inl .destination => .inl destination
    | .inl .scratch => .inr true
    | .inr i => .inl i.val
  invFun
    | .inl i => if h : i = destination then .inl .destination else .inr ⟨i, h⟩
    | .inr false => .inl .source
    | .inr true => .inl .scratch
  left_inv x := by
    cases x with
    | inl k => cases k <;> simp
    | inr i => simp [i.property]
  right_inv x := by
    cases x with
    | inl i => by_cases h : i = destination <;> simp [h]
    | inr bit => cases bit <;> rfl

abbrev Config (s l m : Nat) :=
  Cfg (fun _ : Ports s => Bool) BitPortTransfer.Label ((Fin l × Fin m) × Option Bool)

def program {s l m : Nat} (destination : Fin s) :
    BitPortTransfer.Label → Stmt (fun _ : Ports s => Bool)
      BitPortTransfer.Label ((Fin l × Fin m) × Option Bool) :=
  fun phase => TM2MemoryFrame.liftStmt
    (TM2StackFrame.relocate (layout destination) (BitPortTransfer.program true phase))

def start {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (destination : Fin s)
    (next : Fin l) (answer : List Bool) : Config s l m :=
  TM2MemoryFrame.embed (next, cfg.var)
    (TM2StackFrame.embed (layout destination)
      (BitPortTransfer.config (some .clear) answer (cfg.stk destination) [])
      (fun i => cfg.stk i.val))

def project {s l m : Nat} (cfg : Config s l m) : BitOracleMachine.Config s l m :=
  ⟨some cfg.var.1.1, cfg.var.1.2, fun i => cfg.stk (.inl i)⟩

/-- All original stack contents are present before the transfer; none is preloaded by a premise. -/
theorem start_original {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (destination i : Fin s)
    (next : Fin l) (answer : List Bool) :
    (start cfg destination next answer).stk (.inl i) = cfg.stk i := by
  by_cases h : i = destination <;>
    simp [start, TM2MemoryFrame.embed, TM2StackFrame.embed, TM2StackFrame.data,
      layout, BitPortTransfer.config, BitCopyMachine.config, h]

/-- The incoming word is on its actual private port; scratch starts empty. -/
theorem start_private {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (destination : Fin s)
    (next : Fin l) (answer : List Bool) :
    (start cfg destination next answer).stk (.inr false) = answer ∧
    (start cfg destination next answer).stk (.inr true) = [] := by
  constructor <;> rfl

/-- The transfer derives the complete original resume state and a TM2 execution bound.
The label-none conclusion is required before projecting the saved return address. -/
theorem run_resume {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (destination : Fin s)
    (next : Fin l) (answer : List Bool) :
    ∃ fuel ≤ (cfg.stk destination).length + 3 * answer.length + 4,
      let out := (TM2ReturnLink.tick (program (l := l) (m := m) destination))^[fuel]
        (start cfg destination next answer)
      out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] := by
  obtain ⟨fuel, hf, hr⟩ := BitPortTransfer.consume_run answer (cfg.stk destination) none
  refine ⟨fuel, hf, ?_⟩
  unfold program start
  simp only [TM2MemoryFrame.run, TM2StackFrame.run]
  rw [hr]
  refine ⟨rfl, ?_, rfl, rfl⟩
  apply congrArg (fun tapes => (⟨some next, cfg.var, tapes⟩ : BitOracleMachine.Config s l m))
  funext i
  by_cases h : i = destination <;>
    simp [TM2MemoryFrame.embed, TM2StackFrame.embed, TM2StackFrame.data,
      layout, BitPortTransfer.config, BitCopyMachine.config,
      Function.update, h]



/-- Reverse the source/destination roles to prepare an outgoing request. -/
private def swapRoles : BitCopyMachine.Stack ≃ BitCopyMachine.Stack where
  toFun | .source => .destination | .destination => .source | .scratch => .scratch
  invFun | .source => .destination | .destination => .source | .scratch => .scratch
  left_inv k := by cases k <;> rfl
  right_inv k := by cases k <;> rfl

def requestLayout {s : Nat} (request : Fin s) :
    BitCopyMachine.Stack ⊕ {i : Fin s // i ≠ request} ≃ Ports s :=
  (Equiv.sumCongr swapRoles (Equiv.refl _)).trans (layout request)

def requestProgram {s l m : Nat} (request : Fin s) :
    BitPortTransfer.Label → Stmt (fun _ : Ports s => Bool)
      BitPortTransfer.Label ((Fin l × Fin m) × Option Bool) :=
  fun phase => TM2MemoryFrame.liftStmt
    (TM2StackFrame.relocate (requestLayout request) (BitPortTransfer.program false phase))

def requestStart {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (request : Fin s)
    (next : Fin l) (oldPort : List Bool) : Config s l m :=
  TM2MemoryFrame.embed (next, cfg.var)
    (TM2StackFrame.embed (requestLayout request)
      (BitPortTransfer.config (some .clear) (cfg.stk request) oldPort [])
      (fun i => cfg.stk i.val))

/-- The outbound layout starts with every caller stack intact and the actual old port word. -/
theorem request_start {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (request i : Fin s)
    (next : Fin l) (oldPort : List Bool) :
    (requestStart cfg request next oldPort).stk (.inl i) = cfg.stk i ∧
    (requestStart cfg request next oldPort).stk (.inr false) = oldPort ∧
    (requestStart cfg request next oldPort).stk (.inr true) = [] := by
  refine ⟨?_, rfl, rfl⟩
  by_cases h : i = request <;>
    simp [requestStart, requestLayout, swapRoles, TM2MemoryFrame.embed,
      TM2StackFrame.embed, TM2StackFrame.data, layout, BitPortTransfer.config,
      BitCopyMachine.config, h]

/-- Prepare the actual query word while preserving all caller stacks and saved memory. -/
theorem run_request {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (request : Fin s)
    (next : Fin l) (oldPort : List Bool) :
    ∃ fuel ≤ oldPort.length + 2 * (cfg.stk request).length + 4,
      let out := (TM2ReturnLink.tick (requestProgram (l := l) (m := m) request))^[fuel]
        (requestStart cfg request next oldPort)
      out.l = none ∧ project out = {cfg with l := some next} ∧
        out.stk (.inr false) = cfg.stk request ∧ out.stk (.inr true) = [] := by
  obtain ⟨fuel, hf, hr⟩ := BitPortTransfer.run (cfg.stk request) oldPort none
  refine ⟨fuel, hf, ?_⟩
  unfold requestProgram requestStart
  simp only [TM2MemoryFrame.run, TM2StackFrame.run]
  rw [hr]
  refine ⟨rfl, ?_, rfl, rfl⟩
  apply congrArg (fun tapes => (⟨some next, cfg.var, tapes⟩ : BitOracleMachine.Config s l m))
  funext i
  by_cases h : i = request <;>
    simp [requestLayout, swapRoles, TM2MemoryFrame.embed, TM2StackFrame.embed,
      TM2StackFrame.data, layout, BitPortTransfer.config, BitCopyMachine.config, h]



/-- Exact completed request phase, including the private port and saved local memory. -/
theorem request_state {s l m : Nat} (cfg : BitOracleMachine.Config s l m) (request : Fin s)
    (next : Fin l) (oldPort : List Bool) :
    ∃ fuel ≤ oldPort.length + 2 * (cfg.stk request).length + 4,
      (TM2ReturnLink.tick (requestProgram (l := l) (m := m) request))^[fuel]
        (requestStart cfg request next oldPort) =
      {requestStart cfg request next (cfg.stk request) with l := none} := by
  obtain ⟨fuel, hf, hr⟩ := BitPortTransfer.run (cfg.stk request) oldPort none
  refine ⟨fuel, hf, ?_⟩
  unfold requestProgram requestStart
  rw [TM2MemoryFrame.run, TM2StackFrame.run, hr]
  rfl

/-- The native oracle delivers its answer on the dedicated port; local transfer starts next. -/
def deliver {s l m : Nat} (answer : List Bool) (cfg : Config s l m) : Config s l m :=
  ⟨some .clear, (cfg.var.1, none), Function.update cfg.stk (.inr false) answer⟩

theorem delivery_start {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) (answer word : List Bool) :
    deliver answer {requestStart cfg request next word with l := none} =
      start cfg destination next answer := by
  apply congrArg (fun tapes => (⟨some .clear, ((next, cfg.var), none), tapes⟩ : Config s l m))
  funext port
  cases port with
  | inl i =>
    change Function.update (requestStart cfg request next word).stk (.inr false) answer (.inl i) = _
    simp only [Function.update_of_ne (by simp : (Sum.inl i : Ports s) ≠ .inr false)]
    rw [(request_start cfg request i next word).1]
    exact (start_original cfg destination i next answer).symm
  | inr bit =>
    cases bit with
    | false =>
      change Function.update (requestStart cfg request next word).stk (.inr false) answer (.inr false) = answer
      simp [Function.update]
    | true =>
      change Function.update (requestStart cfg request next word).stk (.inr false) answer (.inr true) = _
      simp only [Function.update_of_ne (by simp : (Sum.inr true : Ports s) ≠ .inr false)]
      rw [(request_start cfg request destination next word).2.2]
      exact (start_private cfg destination next answer).2.symm

/-- Both transfer phases meet the actual resume state and restore empty private ports.
The request-phase fuel is chosen before the answer, preserving the oracle interaction order.
The bound counts TM2 ticks plus the single native oracle event, not TM0 steps. -/
theorem hash_transfer {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) :
    ∃ before ≤ 2 * (cfg.stk request).length + 4,
      let issued := (TM2ReturnLink.tick (requestProgram (l := l) (m := m) request))^[before]
        (requestStart cfg request next [])
      issued.l = none ∧ issued.stk (.inr false) = cfg.stk request ∧
      ∀ answer : List Bool, ∃ after,
        before + 1 + after ≤ 9 * (1 + (cfg.stk request).length +
          (cfg.stk destination).length + answer.length) ∧
        let out := (TM2ReturnLink.tick (program (l := l) (m := m) destination))^[after]
          (deliver answer issued)
        out.l = none ∧ project out = BitOracleMachine.resume cfg destination next answer ∧
          out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] := by
  obtain ⟨before, hb, he⟩ := request_state cfg request next []
  refine ⟨before, by simpa using hb, ?_⟩
  rw [he]
  refine ⟨rfl, (request_start cfg request request next (cfg.stk request)).2.1, ?_⟩
  intro answer
  obtain ⟨after, ha, hout⟩ := run_resume cfg destination next answer
  refine ⟨after, by simp only [List.length_nil, Nat.zero_add] at hb; omega, ?_⟩
  rw [delivery_start]
  exact hout



/-- A native coin answer uses the same consuming transfer and leaves no private word behind. -/
theorem coin_transfer {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) (bit : Bool) :
    ∃ after, 1 + after ≤ 9 * (2 + (cfg.stk destination).length) ∧
      let out := (TM2ReturnLink.tick (program (l := l) (m := m) destination))^[after]
        (deliver [bit] {requestStart cfg destination next [] with l := none})
      out.l = none ∧ project out = BitOracleMachine.resume cfg destination next [bit] ∧
        out.stk (.inr false) = [] ∧ out.stk (.inr true) = [] := by
  obtain ⟨after, ha, hout⟩ := run_resume cfg destination next [bit]
  refine ⟨after, by simp only [List.length_cons, List.length_nil] at ha; omega, ?_⟩
  rw [delivery_start]
  exact hout



/-- Issue the actual raw hash request from the prepared port and deliver its answer. -/
def nativeHash {s l m : Nat} (cfg : Config s l m) : OracleComp BitOracleMachine.spec (Config s l m) := do
  let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk (.inr false))))
  pure (deliver answer cfg)

/-- The prepared physical query and its complete continuation agree with the original raw request. -/
theorem hash_handoff {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (request destination : Fin s) (next : Fin l) :
    ∃ before ≤ 2 * (cfg.stk request).length + 4,
      nativeHash ((TM2ReturnLink.tick (requestProgram (l := l) (m := m) request))^[before]
        (requestStart cfg request next [])) =
      (do let answer ← liftM (BitOracleMachine.spec.query (.hash (cfg.stk request)))
          pure (start cfg destination next answer)) := by
  obtain ⟨before, hb, he⟩ := request_state cfg request next []
  refine ⟨before, by simpa using hb, ?_⟩
  rw [he]
  unfold nativeHash
  rw [(request_start cfg request request next (cfg.stk request)).2.1]
  apply bind_congr
  intro answer
  exact congrArg (pure : Config s l m → OracleComp BitOracleMachine.spec (Config s l m))
    (delivery_start cfg request destination next answer (cfg.stk request))

/-- Issue the actual raw coin query and place its single bit on the native port. -/
def nativeCoin {s l m : Nat} (cfg : Config s l m) : OracleComp BitOracleMachine.spec (Config s l m) := do
  let bit ← liftM (BitOracleMachine.spec.query .coin)
  pure (deliver [bit] cfg)

theorem coin_handoff {s l m : Nat} (cfg : BitOracleMachine.Config s l m)
    (destination : Fin s) (next : Fin l) :
    nativeCoin {requestStart cfg destination next [] with l := none} =
      (do let bit ← liftM (BitOracleMachine.spec.query .coin)
          pure (start cfg destination next [bit])) := by
  unfold nativeCoin
  apply bind_congr
  intro bit
  rw [delivery_start]

end ExplainableCrypto.Helios.Computational.BitOraclePortTransfer
