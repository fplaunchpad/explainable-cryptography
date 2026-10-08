import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveCorrespondence

/-! Finite control at every primitive target state, including intermediate
residual instructions. Only the three tapes may contain unbounded data. -/
namespace ExplainableCrypto.Helios.Computational.BitOraclePrimitiveFinite
open Turing OracleComp OracleSpec BitOraclePortTransfer BitOraclePrimitiveLoop

noncomputable def regionSupport {K L V : Type} [DecidableEq K] [Fintype L] [Fintype V]
    (M : L → TM2.Stmt (fun _ : K => Bool) L V) :=
  TM1to0.trStmts (TM2to1.tr M) (TM2to1.trSupp M Finset.univ)

/-- Target residual instructions belong to the actual compiled program's
finite support. Phase tags, ports, labels and saved memory are already finite. -/
def TargetSupported {s l m : Nat} (code : BitOracleMachine.Code s l m) : State s l m → Prop
  | .compute source cfg _ _ => cfg.q ∈ regionSupport (BitOracleTapeLoop.localProgram code source)
  | .prepare request _ cfg _ _ => cfg.q ∈ regionSupport (requestProgram request)
  | .response destination cfg _ _ => cfg.q ∈ regionSupport (program destination)
  | _ => True

private theorem region_normal {K L V : Type} [DecidableEq K] [Fintype L] [Fintype V]
    (M : L → TM2.Stmt (fun _ : K => Bool) L V) (label : L) (memory : V) :
    (some (TM2to1.tr M (.normal label)), memory) ∈ regionSupport M := by
  classical
  apply Finset.mem_product.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  apply Finset.some_mem_insertNone.mpr
  apply Finset.mem_biUnion.mpr
  refine ⟨.normal label, ?_, TM1.stmts₁_self⟩
  exact Finset.mem_biUnion.mpr ⟨label, Finset.mem_univ _, Finset.mem_insert_self _ _⟩

private theorem region_tick {K L V : Type} [DecidableEq K] [Fintype L] [Fintype V] [Inhabited L]
    (M : L → TM2.Stmt (fun _ : K => Bool) L V) (cfg : PrimitiveConfig K L V)
    (h : cfg.q ∈ regionSupport M) : (primitiveTick (TM2to1.tr M) cfg).q ∈ regionSupport M := by
  let _ : Inhabited V := ⟨cfg.q.2⟩
  have hs := BitOraclePrimitiveCost.finite_support M
  apply (congrArg (fun c : TM0.Cfg (TM2to1.Γ' K (fun _ => Bool)) (TM1to0.Λ' (TM2to1.tr M)) =>
    c.q ∈ regionSupport M) (primitiveTick_eq (TM2to1.tr M) cfg)).mpr
  change ((TM0.step (TM1to0.tr (TM2to1.tr M)) cfg).getD cfg).q ∈ regionSupport M
  cases he : TM0.step (TM1to0.tr (TM2to1.tr M)) cfg with
  | none => exact h
  | some out => exact TM0.step_supports _ hs he h

/-- Every ready entry derives the target invariant, independently of its tapes. -/
theorem ready_supported {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (label : Option (Fin l)) (memory : Fin m) (tapes : OracleTapeDispatch.Tapes (Ports s)) :
    TargetSupported code (.ready label memory tapes) := trivial

/-- Every individual primitive or native successor retains the finite control
invariant. This quantifies over arbitrary answer contents and lengths. -/
theorem target_step_supported {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : State s l m) (h : TargetSupported code cfg) :
    ∀ out ∈ support (step code cfg), TargetSupported code out := by
  let _ : Inhabited BitPortTransfer.Label := ⟨.clear⟩
  cases cfg with
  | ready label memory tapes => cases label with
    | none => simp [step, TargetSupported]
    | some source => cases hc : code source with
      | compute q => simpa [step, hc, TargetSupported] using
          region_normal (BitOracleTapeLoop.localProgram code source) () (some source, memory)
      | coin destination next => simp [step, hc, TargetSupported]
      | hash request destination next =>
        simpa [step, hc, TargetSupported] using
          (region_normal (requestProgram (l := l) (m := m) request) BitPortTransfer.Label.clear
            ((next, memory), none))
  | compute source cfg query answer =>
    by_cases he : cfg.q.1.isNone = true
    · simp [step, he, TargetSupported]
    · simpa [step, he, TargetSupported] using
        region_tick (BitOracleTapeLoop.localProgram code source) cfg h
  | prepare request destination cfg query answer =>
    by_cases he : cfg.q.1.isNone = true
    · simp [step, he, TargetSupported]
    · simpa [step, he, TargetSupported] using region_tick (requestProgram request) cfg h
  | response destination cfg query answer =>
    by_cases he : cfg.q.1.isNone = true
    · simp [step, he, TargetSupported]
    · simpa [step, he, TargetSupported] using region_tick (program destination) cfg h
  | output kind destination saved cfg answer =>
    by_cases he : cfg.phase = .done <;> simp [step, he, TargetSupported]
  | issue kind destination saved tapes => simp [step, TargetSupported]
  | input destination saved query cfg =>
    by_cases he : cfg.phase = .done
    · simpa [step, he, TargetSupported] using
        (region_normal (program (l := l) (m := m) destination) BitPortTransfer.Label.clear (saved, none))
    · simp [step, he, TargetSupported]

/-- The invariant covers every state after any finite primitive run, including
states inside deterministic regions, rather than only lowering boundaries. -/
theorem target_run_supported {s l m : Nat} (code : BitOracleMachine.Code s l m) (fuel : Nat)
    (cfg : State s l m) (h : TargetSupported code cfg) :
    ∀ out ∈ support (run code fuel cfg), TargetSupported code out := by
  induction fuel generalizing cfg with
  | zero => simpa [run] using h
  | succ fuel ih =>
    intro out ho
    obtain ⟨next, hn, hr⟩ := OracleComp.mem_support_bind_peel _ _ ho
    exact ih next (target_step_supported code cfg h next hn) out hr

/-- Proof-only projection retaining every control field while replacing all
three tapes by fixed blanks. It is not an executed instruction or decoder. -/
def control {s l m : Nat} : State s l m → State s l m
  | .ready label memory _ => .ready label memory ⟨default, default, default⟩
  | .compute source cfg _ _ => .compute source ⟨cfg.q, default⟩ default default
  | .prepare request destination cfg _ _ => .prepare request destination ⟨cfg.q, default⟩ default default
  | .response destination cfg _ _ => .response destination ⟨cfg.q, default⟩ default default
  | .output kind destination saved cfg _ => .output kind destination saved ⟨cfg.phase, default, default⟩ default
  | .issue kind destination saved _ => .issue kind destination saved ⟨default, default, default⟩
  | .input destination saved _ cfg => .input destination saved default ⟨cfg.phase, default, default⟩

/-- Read the three unbounded storage fields for the representation theorem.
This is proof-side projection, not a runtime operation. -/
def tapes {s l m : Nat} : State s l m → OracleTapeDispatch.Tapes (Ports s)
  | .ready _ _ t | .issue _ _ _ t => t
  | .compute _ cfg query answer | .prepare _ _ cfg query answer | .response _ cfg query answer =>
      ⟨cfg.Tape, query, answer⟩
  | .output _ _ _ cfg answer => ⟨cfg.work, cfg.query, answer⟩
  | .input _ _ query cfg => ⟨cfg.work, query, cfg.answer⟩

/-- Reconstruct the unchanged target representation from its control and tapes. -/
def withTapes {s l m : Nat} (t : OracleTapeDispatch.Tapes (Ports s)) : State s l m → State s l m
  | .ready label memory _ => .ready label memory t
  | .compute source cfg _ _ => .compute source ⟨cfg.q, t.work⟩ t.query t.answer
  | .prepare request destination cfg _ _ => .prepare request destination ⟨cfg.q, t.work⟩ t.query t.answer
  | .response destination cfg _ _ => .response destination ⟨cfg.q, t.work⟩ t.query t.answer
  | .output kind destination saved cfg _ => .output kind destination saved ⟨cfg.phase, t.work, t.query⟩ t.answer
  | .issue kind destination saved _ => .issue kind destination saved t
  | .input destination saved _ cfg => .input destination saved t.query ⟨cfg.phase, t.work, t.answer⟩

/-- The finite-control projection omits no non-tape field. Every original
state is recovered, including intermediate instructions and saved memory. -/
theorem reconstruct {s l m : Nat} (cfg : State s l m) : withTapes (tapes cfg) (control cfg) = cfg := by
  cases cfg <;> rfl

/-- Both the work alphabet and native tape alphabet are finite for fixed ports. -/
theorem alphabets_finite (s : Nat) :
    Finite (TM2to1.Γ' (Ports s) (fun _ => Bool)) ∧ Finite (Option Bool) :=
  ⟨inferInstance, inferInstance⟩

private instance : Fintype OracleTapeDispatch.Kind :=
  ⟨{.hash, .coin}, by intro kind; cases kind <;> simp⟩

/-- Enumerate only control, with residual instructions restricted to each
fixed compiler support. No tape-content bound is used in this finite set. -/
noncomputable def controlSupport {s l m : Nat} (code : BitOracleMachine.Code s l m) : Finset (State s l m) := by
  classical
  exact
    (Finset.univ.image (fun x : Option (Fin l) × Fin m => State.ready x.1 x.2 ⟨default, default, default⟩)) ∪
    (Finset.univ.biUnion (fun source : Fin l =>
      (regionSupport (BitOracleTapeLoop.localProgram code source)).image
        (fun q => State.compute source ⟨q, default⟩ default default))) ∪
    (Finset.univ.biUnion (fun request : Fin s => Finset.univ.biUnion (fun destination : Fin s =>
      (regionSupport (requestProgram (l := l) (m := m) request)).image
        (fun q => State.prepare request destination ⟨q, default⟩ default default)))) ∪
    (Finset.univ.image (fun x : OracleTapeDispatch.Kind × Fin s × (Fin l × Fin m) × OracleTapeOutput.Phase =>
      State.output x.1 x.2.1 x.2.2.1 ⟨x.2.2.2, default, default⟩ default)) ∪
    (Finset.univ.image (fun x : OracleTapeDispatch.Kind × Fin s × (Fin l × Fin m) =>
      State.issue x.1 x.2.1 x.2.2 ⟨default, default, default⟩)) ∪
    (Finset.univ.image (fun x : Fin s × (Fin l × Fin m) × OracleTapeInput.Phase =>
      State.input x.1 x.2.1 default ⟨x.2.2, default, default⟩)) ∪
    (Finset.univ.biUnion (fun destination : Fin s =>
      (regionSupport (program (l := l) (m := m) destination)).image
        (fun q => State.response destination ⟨q, default⟩ default default)))

/-- Every supported target control belongs to the one code-derived finite
set, retaining all phase tags, residual statements and saved caller memory. -/
theorem finite_control {s l m : Nat} (code : BitOracleMachine.Code s l m)
    (cfg : State s l m) (h : TargetSupported code cfg) : control cfg ∈ controlSupport code := by
  classical
  cases cfg <;> simp [control, controlSupport, Finset.mem_image, Finset.mem_biUnion, TargetSupported] at h ⊢
  case compute source cfg query answer =>
    exact Or.inl ⟨source, Finset.mem_image.mpr ⟨cfg.q, h, rfl⟩⟩
  case prepare request destination cfg query answer =>
    exact Or.inr (Or.inl ⟨request, destination, Finset.mem_image.mpr ⟨cfg.q, h, rfl⟩⟩)
  case response destination cfg query answer =>
    exact Or.inr (Or.inr ⟨destination, Finset.mem_image.mpr ⟨cfg.q, h, rfl⟩⟩)

/-- Every reachable primitive target state has finite control, regardless of
its initial words, native answer sizes or the point where execution is observed. -/
theorem reachable_control {s l m : Nat} (code : BitOracleMachine.Code s l m) (fuel : Nat)
    (label : Option (Fin l)) (memory : Fin m) (tapes : OracleTapeDispatch.Tapes (Ports s)) :
    ∀ out ∈ support (run code fuel (.ready label memory tapes)), control out ∈ controlSupport code :=
  fun out ho => finite_control code out
    (target_run_supported code fuel _ (ready_supported code label memory tapes) out ho)

end ExplainableCrypto.Helios.Computational.BitOraclePrimitiveFinite
