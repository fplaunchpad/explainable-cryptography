import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Ordinary three-symbol TM0 tape computation in the existing bit-source
language. This is the local-computation component of attacker coverage;
oracle interface conversion and complete PPT coverage remain separate. -/
namespace ExplainableCrypto.Helios.Computational.BitTapeCoverage
open Turing OracleComp OracleSpec

abbrev Cell := Option Bool

def cellCode : Cell → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

def readCell (v : Fin 3) : Cell := if v = 0 then none else some (v = 2)

private theorem read_code (c : Cell) : readCell (cellCode c) = c := by
  cases c with
  | none => rfl
  | some b => cases b <;> rfl

def cells : List Cell → List Bool
  | [] => []
  | c :: rest => c.isSome :: c.getD false :: cells rest

/-- Finite representatives of the two tape sides, nearest cell first. -/
structure Config (l : Nat) where
  label : Option (Fin l)
  head : Cell
  before : List Cell
  after : List Cell

/-- Proof-side representation, not a runtime input conversion. -/
def present {l : Nat} (c : Config l) : BitOracleMachine.Config 2 l 3 :=
  ⟨c.label, cellCode c.head, ![cells c.before, cells c.after]⟩

def tape {l : Nat} (c : Config l) : Tape Cell :=
  ⟨c.head, ListBlank.mk c.before, ListBlank.mk c.after⟩

/-- Every cell has two stored bits; omitted tail cells denote native blanks. -/
theorem cells_length (word : List Cell) : (cells word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons bit word ih => simp [cells, ih]; omega

/-- Every tape in the pinned model has a finite representative of this form.
This is a proof-side existence result, not a free executable input converter. -/
theorem represents_every_tape {l : Nat} (label : Option (Fin l)) (T : Tape Cell) :
    ∃ c : Config l, c.label = label ∧ tape c = T := by
  cases T with
  | mk head before after =>
    induction before using Quotient.inductionOn' with
    | h before =>
      induction after using Quotient.inductionOn' with
      | h after => exact ⟨⟨label, head, before, after⟩, rfl, rfl⟩

private def finish {l : Nat} (next : Fin l) : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin l) (Fin 3) :=
  .goto (fun _ => next)

private def pushCell {l : Nat} (port : Fin 2)
    (q : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin l) (Fin 3)) :=
  TM2.Stmt.push port (fun v => (readCell v).getD false)
    (.push port (fun v => (readCell v).isSome) q)

private def popCell {l : Nat} (port : Fin 2)
    (q : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin l) (Fin 3)) :=
  TM2.Stmt.pop port (fun _ tag => if tag.getD false then 1 else 0)
    (.pop port (fun v bit => if v = 0 then 0 else cellCode (some (bit.getD false))) q)

private def action {l : Nat} (next : Fin l) :
    TM0.Stmt Cell → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin l) (Fin 3)
  | .write c => .load (fun _ => cellCode c) (finish next)
  | .move .left => pushCell 1 (popCell 0 (finish next))
  | .move .right => pushCell 0 (popCell 1 (finish next))

private def command {l : Nat} : Option (Fin l × TM0.Stmt Cell) →
    TM2.Stmt (fun _ : Fin 2 => Bool) (Fin l) (Fin 3)
  | none => .halt
  | some (next, a) => action next a

/-- Only a finite three-way head test selects a native transition. -/
def program {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l)) (q : Fin l) :
    TM2.Stmt (fun _ : Fin 2 => Bool) (Fin l) (Fin 3) :=
  .branch (fun v => v = 0) (command (M q none))
    (.branch (fun v => v = 1) (command (M q (some false))) (command (M q (some true))))

def advance {l : Nat} (c : Config l) (next : Fin l) : TM0.Stmt Cell → Config l
  | .write bit => {c with label := some next, head := bit}
  | .move .left => ⟨some next, c.before.head?.getD none, c.before.tail, c.head :: c.after⟩
  | .move .right => ⟨some next, c.after.head?.getD none, c.head :: c.before, c.after.tail⟩

def tick {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l)) (c : Config l) : Config l :=
  match c.label with
  | none => c
  | some q => match M q c.head with
    | none => {c with label := none}
    | some (next, a) => advance c next a

private theorem update_left (a b word : List Bool) :
    Function.update ![a, b] (0 : Fin 2) word = ![word, b] := by
  funext k; fin_cases k <;> simp [Function.update]

private theorem update_right (a b word : List Bool) :
    Function.update ![a, b] (1 : Fin 2) word = ![a, word] := by
  funext k; fin_cases k <;> simp [Function.update]

private theorem code_none : cellCode none = 0 := rfl

private theorem code_restore (c : Cell) :
    (if c = none then 0 else cellCode (some (c.getD false))) = cellCode c := by
  cases c with
  | none => rfl
  | some b => cases b <;> rfl

private theorem command_step {l : Nat} (c : Config l)
    (out : Option (Fin l × TM0.Stmt Cell)) :
    TM2.stepAux (command out) (present c).var (present c).stk =
      present (match out with
        | none => {c with label := none}
        | some (next, a) => advance c next a) := by
  cases out with
  | none => rfl
  | some pair =>
    rcases pair with ⟨next, a⟩
    cases a with
    | write bit => rfl
    | move d =>
      cases d <;> cases c with
      | mk label head before after =>
        cases before <;> cases after <;>
          simp [command, action, pushCell, popCell, finish, TM2.stepAux, present,
            advance, cells, read_code, update_left, update_right, code_restore, code_none]

/-- Every source transition realizes the native action, preserving both full
sides and the current cell, including motion into previously blank storage. -/
theorem source_step {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l)) (c : Config l) :
    TM2ReturnLink.tick (program M) (present c) = present (tick M c) := by
  cases c with
  | mk label head before after => cases label with
    | none => rfl
    | some q =>
      cases head with
      | none => exact command_step ⟨some q, none, before, after⟩ _
      | some bit => cases bit with
        | false => exact command_step ⟨some q, some false, before, after⟩ _
        | true => exact command_step ⟨some q, some true, before, after⟩ _

/-- A native move/write is exactly Mathlib's tape operation. -/
theorem advance_tape {l : Nat} (c : Config l) (next : Fin l) (a : TM0.Stmt Cell) :
    tape (advance c next a) = match a with
      | .write bit => (tape c).write bit
      | .move d => (tape c).move d := by
  cases c with
  | mk label head before after =>
    cases a with
    | write => rfl
    | move d => cases d <;> cases before <;> cases after <;> rfl

/-- At a live label the represented transition is exactly the pinned TM0 step.
A native halt retains its final tape and records the terminal label. -/
theorem native_step {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l))
    (c : Config l) (q : Fin l) (hq : c.label = some q) :
    ((tick M c).label, tape (tick M c)) =
      match TM0.step M ⟨q, tape c⟩ with
      | none => (none, tape c)
      | some out => (some out.q, out.Tape) := by
  simp only [tick, hq, TM0.step]
  rw [show (tape c).head = c.head from rfl]
  cases he : M q c.head with
  | none => rfl
  | some pair =>
    rcases pair with ⟨next, a⟩
    rw [advance_tape]
    cases a with
    | write => rfl
    | move d => cases d <;> rfl

/-- Arbitrary finite native computations are represented by actual source
execution, without a caller-supplied correspondence certificate. -/
theorem source_run {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l)) (fuel : Nat) (c : Config l) :
    (TM2ReturnLink.tick (program M))^[fuel] (present c) = present ((tick M)^[fuel] c) := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply, source_step, ih, Function.iterate_succ_apply]

/-- A uniform fixed bound includes both head-selection branches and every
cell bit push/pop; it is independent of tape contents and security parameter. -/
theorem local_cost {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l)) (q : Fin l) :
    BitOracleMachine.localCost (program M q) ≤ 7 := by
  have hc (out : Option (Fin l × TM0.Stmt Cell)) :
      BitOracleMachine.localCost (command out) ≤ 5 := by
    cases out with
    | none => simp [command, BitOracleMachine.localCost]
    | some pair => rcases pair with ⟨next, a⟩; cases a with
      | write => simp [command, action, finish, BitOracleMachine.localCost]
      | move d => cases d <;> simp [command, action, pushCell, popCell, finish, BitOracleMachine.localCost]
  have h0 := hc (M q none)
  have h1 := hc (M q (some false))
  have h2 := hc (M q (some true))
  simp only [program, BitOracleMachine.localCost]
  omega

/-- The actual raw-oracle source run is pure for this native deterministic
program, with the complete represented result and derived charge ≤7 times fuel. -/
theorem charged_run {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l))
    (fuel : Nat) (c : Config l) :
    ∃ charge ≤ 7 * fuel,
      BitOracleMachine.run (fun q => .compute (program M q)) fuel (present c) =
        pure (present ((tick M)^[fuel] c), charge) := by
  obtain ⟨charge, hc, he⟩ := BitOracleMachine.compute_run_cost (program M) 7 (local_cost M) fuel (present c)
  rw [source_run] at he
  exact ⟨charge, hc, he⟩

/-- A native halting run derives the source contract consumed by the existing
primitive compiler; the source bound is not a caller cost certificate. -/
theorem within {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l))
    (fuel limit : Nat) (c : Config l) (halted : ((tick M)^[fuel] c).label = none) :
    BitOracleLoopBounded.Within limit (7 * fuel)
      (BitOracleMachine.run (fun q => .compute (program M q)) fuel (present c)) := by
  obtain ⟨charge, hc, he⟩ := charged_run M fuel c
  rw [he]
  exact ⟨halted, hc⟩

/-- Compose native computation with the existing actual primitive loop. The
native halt condition derives every source-cost premise of this transport. -/
theorem primitive_run {l : Nat} [NeZero l] (M : TM0.Machine Cell (Fin l))
    (fuel limit : Nat) (c : Config l) (halted : ((tick M)^[fuel] c).label = none) :
    let code : BitOracleMachine.Code 2 l 3 := fun q => .compute (program M q)
    let clock := BitOracleTapeCap.unitCost (TM2TapeRuns.height (present c).stk + 7 * fuel + 0) *
      (7 * fuel) * BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code clock (BitOraclePrimitiveLoop.lower code
        (BitOracleTapeLoop.ready (present c) (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      pure (some (present ((tick M)^[fuel] c))) := by
  have he := BitOraclePrimitiveBounded.run_source_bounded (fun q => .compute (program M q))
    fuel limit (7 * fuel) (present c) [] (OracleTapeOutput.wordTape []) (within M fuel limit c halted)
  obtain ⟨charge, _, hr⟩ := charged_run M fuel c
  rw [hr] at he
  simpa only [simulateQ_pure, map_pure, List.length_nil] using he

end ExplainableCrypto.Helios.Computational.BitTapeCoverage
