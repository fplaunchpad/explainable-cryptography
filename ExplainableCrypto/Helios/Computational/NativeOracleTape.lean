import ExplainableCrypto.Helios.Computational.OracleTapeDispatch
import VCVio.OracleComp.EvalDist

/-! A concrete three-tape native oracle reference for attacker coverage.
Code reads only finite labels/current cells. Calls reuse the existing native
raw-word dispatch; source compilation of this interface remains separate. -/
namespace ExplainableCrypto.Helios.Computational.NativeOracleTape
open Turing OracleComp OracleSpec
open OracleTapeOutput (wordTape)

abbrev Cell := Option Bool

structure Config (l : Nat) where
  label : Option (Fin l)
  work : Tape Cell
  query : Tape Cell
  answer : Tape Cell

/-- The only data available to the local transition table. -/
def heads {l : Nat} (c : Config l) : Fin 3 → Cell :=
  ![c.work.head, c.query.head, c.answer.head]

inductive Command (l : Nat) where
  | halt
  | local (next : Fin l) (actions : Fin 3 → Option (TM0.Stmt Cell))
  | oracle (kind : OracleTapeDispatch.Kind) (next : Fin l)

abbrev Code (l : Nat) := Fin l → (Fin 3 → Cell) → Command l

private def act (a : Option (TM0.Stmt Cell)) (t : Tape Cell) : Tape Cell :=
  match a with
  | none => t
  | some (.move d) => t.move d
  | some (.write bit) => t.write bit

/-- Native dispatch never inspects its work component. A fixed unused component
lets this reference reuse that event exactly while retaining its actual work
input. This is a semantic adapter, not an executed work-tape conversion. -/
private def dispatch {l : Nat} (kind : OracleTapeDispatch.Kind) (next : Fin l) (c : Config l) :
    OracleComp BitOracleMachine.spec (Config l) := do
  let out ← OracleTapeDispatch.dispatch kind
    (⟨default, c.query, c.answer⟩ : OracleTapeDispatch.Tapes Unit)
  pure ⟨some next, c.work, out.query, out.answer⟩

def step {l : Nat} (code : Code l) (c : Config l) : OracleComp BitOracleMachine.spec (Config l) :=
  match c.label with
  | none => pure c
  | some q => match code q (heads c) with
    | .halt => pure {c with label := none}
    | .local next actions => pure ⟨some next, act (actions 0) c.work,
        act (actions 1) c.query, act (actions 2) c.answer⟩
    | .oracle kind next => dispatch kind next c

def run {l : Nat} (code : Code l) : Nat → Config l → OracleComp BitOracleMachine.spec (Config l)
  | 0, c => pure c
  | n + 1, c => do
      let next ← step code c
      run code n next

def initial {l : Nat} (entry : Fin l) (word : List Bool) : Config l :=
  ⟨some entry, wordTape word, wordTape [], wordTape []⟩

/-- Finite current-cell inputs exclude arbitrary local host callbacks on tapes. -/
theorem heads_finite (l : Nat) : Finite (Fin l × (Fin 3 → Cell)) := inferInstance

/-- The possible commands are finite too: three optional primitive actions,
finite return labels, and two native event kinds. -/
theorem commands_finite (l : Nat) : Finite (Command l) := by
  let _ : Finite (TM0.Stmt Cell) := Finite.of_surjective
    (fun x : Bool ⊕ Cell => match x with
      | .inl false => TM0.Stmt.move .left
      | .inl true => TM0.Stmt.move .right
      | .inr bit => TM0.Stmt.write bit) (by
        intro a
        cases a with
        | move d => cases d with
          | left => exact ⟨.inl false, rfl⟩
          | right => exact ⟨.inl true, rfl⟩
        | write bit => exact ⟨.inr bit, rfl⟩)
  apply Finite.of_surjective (fun x : Option ((Fin l × (Fin 3 → Option (TM0.Stmt Cell))) ⊕
      (Bool × Fin l)) => match x with
    | none => Command.halt
    | some (.inl (next, actions)) => Command.local next actions
    | some (.inr (false, next)) => Command.oracle .hash next
    | some (.inr (true, next)) => Command.oracle .coin next)
  intro cmd
  cases cmd with
  | halt => exact ⟨none, rfl⟩
  | «local» next actions => exact ⟨some (.inl (next, actions)), rfl⟩
  | oracle kind next => cases kind with
    | hash => exact ⟨some (.inr (false, next)), rfl⟩
    | coin => exact ⟨some (.inr (true, next)), rfl⟩

/-- The selected ordinary command executes only its specified head-local actions. -/
theorem local_step {l : Nat} (code : Code l) (c : Config l) (q next : Fin l)
    (actions : Fin 3 → Option (TM0.Stmt Cell)) (hq : c.label = some q)
    (hc : code q (heads c) = .local next actions) :
    step code c = pure ⟨some next, act (actions 0) c.work,
      act (actions 1) c.query, act (actions 2) c.answer⟩ := by
  simp [step, hq, hc]

/-- Exact raw hash event and complete successor, including preserved work/query. -/
theorem hash_step {l : Nat} (code : Code l) (c : Config l) (q next : Fin l)
    (hq : c.label = some q) (hc : code q (heads c) = .oracle .hash next) :
    step code c = (do
      let answer ← liftM (BitOracleMachine.spec.query (.hash (OracleTapeDispatch.readWord c.query)))
      pure (⟨some next, c.work, c.query, wordTape answer⟩ : Config l)) := by
  simp only [step, hq, hc, dispatch, OracleTapeDispatch.dispatch, bind_assoc, pure_bind]
  rfl

/-- Coins replace the answer tape by the actual one-bit word. -/
theorem coin_step {l : Nat} (code : Code l) (c : Config l) (q next : Fin l)
    (hq : c.label = some q) (hc : code q (heads c) = .oracle .coin next) :
    step code c = (do
      let bit ← liftM (BitOracleMachine.spec.query .coin)
      pure (⟨some next, c.work, c.query, wordTape [bit]⟩ : Config l)) := by
  simp only [step, hq, hc, dispatch, OracleTapeDispatch.coin_word, bind_assoc, pure_bind]

/-- Every native reply preserves the complete work/query tapes and resumes
at the selected label; no frame or canonical-query premise is assumed. -/
theorem oracle_successor {l : Nat} (code : Code l) (c out : Config l) (q next : Fin l)
    (kind : OracleTapeDispatch.Kind) (hq : c.label = some q)
    (hc : code q (heads c) = .oracle kind next) (ho : out ∈ support (step code c)) :
    ∃ word, out = ⟨some next, c.work, c.query, wordTape word⟩ := by
  cases kind with
  | hash =>
    rw [hash_step code c q next hq hc] at ho
    obtain ⟨word, _, he⟩ := OracleComp.mem_support_bind_peel _ _ ho
    exact ⟨word, by simpa using he⟩
  | coin =>
    rw [coin_step code c q next hq hc] at ho
    obtain ⟨bit, _, he⟩ := OracleComp.mem_support_bind_peel _ _ ho
    exact ⟨[bit], by simpa using he⟩

/-- Arbitrary bounded observations compose without hiding intermediate calls. -/
theorem run_add {l : Nat} (code : Code l) (a b : Nat) (c : Config l) :
    run code (a + b) c = (run code a c >>= run code b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih => simp [Nat.succ_add, run, ih, bind_assoc]

/-- Terminal native states are absorbing; their complete tapes are retained. -/
theorem run_halted {l : Nat} (code : Code l) (n : Nat) (c : Config l) (h : c.label = none) :
    run code n c = pure c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, step, h, ih]

end ExplainableCrypto.Helios.Computational.NativeOracleTape
