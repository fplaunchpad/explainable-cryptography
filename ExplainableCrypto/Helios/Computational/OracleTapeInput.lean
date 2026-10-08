import ExplainableCrypto.Helios.Computational.OracleTapeOutput

/-! Physical answer replacement, reusing Mathlib's proved top-of-stack updates.
Each transition operates only on current cells and unit head movements. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeInput
open Turing TM2to1 TM2TapeRuns OracleTapeOutput

inductive Phase where
  | seekWork | erase | eraseCell | seekAnswer | loadLeft | write | back | done
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.seekWork, .erase, .eraseCell, .seekAnswer, .loadLeft, .write, .back, .done},
    by intro p; cases p <;> simp⟩

structure Config (K : Type*) where
  phase : Phase
  work : WorkTape K
  answer : Tape (Option Bool)

private def writePort {K : Type*} [DecidableEq K] (work : WorkTape K)
    (port : K) (bit : Option Bool) : WorkTape K :=
  Tape.write (Γ := Γ' K (fun _ => Bool))
    (work.head.1, Function.update work.head.2 port bit) work

def step {K : Type*} [DecidableEq K] (port : K) (c : Config K) : Config K :=
  match c.phase with
  | .seekWork => match c.work.head.2 port with
    | some _ => ⟨.seekWork, c.work.move .right, c.answer⟩
    | none => ⟨.erase, c.work, c.answer⟩
  | .erase => if c.work.head.1 then ⟨.seekAnswer, c.work, c.answer⟩
      else ⟨.eraseCell, c.work.move .left, c.answer⟩
  | .eraseCell => ⟨.erase,
      writePort c.work port none, c.answer⟩
  | .seekAnswer => match c.answer.head with
    | some _ => ⟨.seekAnswer, c.work, c.answer.move .right⟩
    | none => ⟨.loadLeft, c.work, c.answer⟩
  | .loadLeft => ⟨.write, c.work, c.answer.move .left⟩
  | .write => match c.answer.head with
    | some bit => ⟨.loadLeft,
        (writePort c.work port (some bit)).move .right,
        c.answer⟩
    | none => ⟨.back, c.work, c.answer.move .right⟩
  | .back => if c.work.head.1 then ⟨.done, c.work, c.answer⟩
      else ⟨.back, c.work.move .left, c.answer⟩
  | .done => c

private def base {K : Type*} [Fintype K] (S : K → List Bool) : WorkTape K :=
  Tape.mk' ∅ (addBottom (columns S))

private theorem presented_columns {K : Type*} [Fintype K]
    (S : K → List Bool) (L : ListBlank (K → Option Bool))
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    L = columns S := by
  apply ListBlank.ext
  intro n
  funext k
  rw [stk_nth_val n (hL k), columns_nth]

private theorem push_top {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (bit : Bool) :
    let W := (Tape.move .right)^[(S port).length] (base S)
    (writePort W port (some bit)).move .right =
      (Tape.move .right)^[(S port).length + 1]
        (base (Function.update S port (bit :: S port))) := by
  obtain ⟨L, hL, he⟩ := tr_respects_aux₂
    (Λ := Unit) (q := TM1.Stmt.halt) (v := ()) (S := S)
    (columns_presentation S) (StAct.push (fun _ : Unit => bit) : StAct K (fun _ => Bool) Unit port)
  have ht := congrArg TM1.Cfg.Tape he
  simp only [trStAct, TM1.stepAux] at ht
  have hl := presented_columns (Function.update S port (bit :: S port)) L hL
  rw [hl] at ht
  simpa only [base, writePort, Function.update_self, stWrite, List.length_cons] using ht

private theorem pop_top {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (bit : Bool) (rest : List Bool)
    (hs : S port = bit :: rest) :
    let W := ((Tape.move .right)^[(S port).length] (base S)).move .left
    writePort W port none =
      (Tape.move .right)^[rest.length] (base (Function.update S port rest)) := by
  obtain ⟨L, hL, he⟩ := tr_respects_aux₂
    (Λ := Unit) (q := TM1.Stmt.halt) (v := ()) (S := S)
    (columns_presentation S) (StAct.pop (fun _ : Unit => fun _ => ()) : StAct K (fun _ => Bool) Unit port)
  have ht := congrArg TM1.Cfg.Tape he
  have hm : ((Tape.move .right)^[(S port).length] (base S)).head.1 = false := by
    rw [hs]
    change ((Tape.move .right)^[rest.length + 1] (base S)).head.1 = false
    rw [base, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst]
  simp only [trStAct, TM1.stepAux] at ht
  dsimp only [base] at hm
  rw [hm] at ht
  have hl := presented_columns (Function.update S port rest) L (by simpa [stWrite, hs] using hL)
  rw [hl] at ht
  simpa [base, writePort, stWrite, hs] using ht

private theorem base_read {K : Type*} [Fintype K] (S : K → List Bool) (port : K) (i : Nat) :
    ((Tape.move .right)^[i] (base S)).head.2 port = (S port).reverse[i]? := by
  rw [base, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd, columns_nth]

private theorem base_mark {K : Type*} [Fintype K] (S : K → List Bool) (i : Nat) :
    ((Tape.move .right)^[i] (base S)).head.1 = (i == 0) := by
  cases i with
  | zero => rfl
  | succ i =>
    rw [base, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst]
    rfl

private theorem seek_work_prefix {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (answer : Tape (Option Bool))
    (n : Nat) (hn : n ≤ (S port).length) :
    (step port)^[n] ⟨.seekWork, base S, answer⟩ =
      ⟨.seekWork, (Tape.move .right)^[n] (base S), answer⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hn' : n < (S port).reverse.length := by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    simp only [step, base_read, List.getElem?_eq_getElem hn']
    rw [Function.iterate_succ_apply']

private theorem seek_work_run {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (answer : Tape (Option Bool)) :
    (step port)^[(S port).length + 1] ⟨.seekWork, base S, answer⟩ =
      ⟨.erase, (Tape.move .right)^[(S port).length] (base S), answer⟩ := by
  rw [Function.iterate_succ_apply', seek_work_prefix S port answer _ le_rfl]
  simp only [step, base_read, List.getElem?_eq_none (by simp : (S port).reverse.length ≤ (S port).length)]

private theorem erase_run {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (word : List Bool) (answer : Tape (Option Bool)) :
    (step port)^[2 * word.length + 1]
        ⟨.erase, (Tape.move .right)^[word.length] (base (Function.update S port word)), answer⟩ =
      ⟨.seekAnswer, base (Function.update S port []), answer⟩ := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    have hm := base_mark (Function.update S port (bit :: word)) (word.length + 1)
    have hs : (step port)^[2]
        ⟨.erase, (Tape.move .right)^[word.length + 1] (base (Function.update S port (bit :: word))), answer⟩ =
        ⟨.erase, (Tape.move .right)^[word.length] (base (Function.update S port word)), answer⟩ := by
      change step port (step port ⟨.erase,
        (Tape.move .right)^[word.length + 1] (base (Function.update S port (bit :: word))), answer⟩) = _
      have one : step port ⟨.erase,
          (Tape.move .right)^[word.length + 1] (base (Function.update S port (bit :: word))), answer⟩ =
          ⟨.eraseCell, ((Tape.move .right)^[word.length + 1]
            (base (Function.update S port (bit :: word)))).move .left, answer⟩ := by
        simp only [step, hm, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte]
      rw [one]
      change (⟨.erase, writePort (((Tape.move .right)^[word.length + 1]
        (base (Function.update S port (bit :: word)))).move .left) port none, answer⟩ : Config K) = _
      have hp := pop_top (Function.update S port (bit :: word)) port bit word (Function.update_self ..)
      simp only [Function.update_self, Function.update_idem, List.length_cons] at hp
      rw [hp]
    have ht : 2 * (bit :: word).length + 1 = (2 * word.length + 1) + 2 := by simp; omega
    rw [ht, Function.iterate_add_apply]
    simp only [List.length_cons]
    rw [hs, ih]

private def cursor (left right : List Bool) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk (left.map some)) (ListBlank.mk (right.map some))

private theorem cursor_nil (word : List Bool) : cursor [] word = wordTape word := rfl

private theorem cursor_left (bit : Bool) (left right : List Bool) :
    (cursor (bit :: left) right).move .left = cursor left (bit :: right) := by
  rw [cursor, Tape.move_left_mk']
  rfl

private theorem seek_answer_run {K : Type*} [DecidableEq K] (port : K)
    (work : WorkTape K) (word left : List Bool) :
    (step port)^[word.length + 1] ⟨.seekAnswer, work, cursor left word⟩ =
      ⟨.loadLeft, work, cursor (word.reverse ++ left) []⟩ := by
  induction word generalizing left with
  | nil => rfl
  | cons bit word ih =>
    rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply]
    change (step port)^[word.length + 1] ⟨.seekAnswer, work, cursor (bit :: left) word⟩ = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem load_run {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (left right acc : List Bool) :
    (step port)^[2 * left.length + 2]
        ⟨.loadLeft, (Tape.move .right)^[acc.length] (base (Function.update S port acc)), cursor left right⟩ =
      ⟨.back, (Tape.move .right)^[(left.reverse ++ acc).length]
        (base (Function.update S port (left.reverse ++ acc))), wordTape (left.reverse ++ right)⟩ := by
  induction left generalizing right acc with
  | nil =>
    change (⟨.back, _, ((cursor [] right).move .left).move .right⟩ : Config K) = _
    rw [Tape.move_left_right]
    rfl
  | cons bit left ih =>
    have hs : (step port)^[2]
        ⟨.loadLeft, (Tape.move .right)^[acc.length] (base (Function.update S port acc)), cursor (bit :: left) right⟩ =
        ⟨.loadLeft, (Tape.move .right)^[(bit :: acc).length]
          (base (Function.update S port (bit :: acc))), cursor left (bit :: right)⟩ := by
      change step port (step port ⟨.loadLeft,
        (Tape.move .right)^[acc.length] (base (Function.update S port acc)), cursor (bit :: left) right⟩) = _
      have one : step port ⟨.loadLeft,
          (Tape.move .right)^[acc.length] (base (Function.update S port acc)), cursor (bit :: left) right⟩ =
          ⟨.write, (Tape.move .right)^[acc.length] (base (Function.update S port acc)), cursor left (bit :: right)⟩ := by
        dsimp only [step]
        rw [cursor_left]
      rw [one]
      change (⟨.loadLeft,
        (writePort ((Tape.move .right)^[acc.length] (base (Function.update S port acc))) port (some bit)).move .right,
        cursor left (bit :: right)⟩ : Config K) = _
      have hp := push_top (Function.update S port acc) port bit
      simp only [Function.update_self, Function.update_idem] at hp
      rw [hp]
      rfl
    have ht : 2 * (bit :: left).length + 2 = (2 * left.length + 2) + 2 := by simp; omega
    rw [ht, Function.iterate_add_apply, hs, ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem back_run {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (answer : Tape (Option Bool)) (n : Nat) :
    (step port)^[n + 1] ⟨.back, (Tape.move .right)^[n] (base S), answer⟩ =
      ⟨.done, base S, answer⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hs : step port ⟨.back, (Tape.move .right)^[n + 1] (base S), answer⟩ =
        ⟨.back, (Tape.move .right)^[n] (base S), answer⟩ := by
      simp only [step, base_mark, beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte]
      rw [Function.iterate_succ_apply', Tape.move_right_left]
    rw [hs, ih]

/-- Exact physical replacement of an existing work column by a native answer.
Both complete tapes and their head positions appear in the conclusion. -/
private theorem run {K : Type*} [DecidableEq K] [Fintype K]
    (S : K → List Bool) (port : K) (answer : List Bool) :
    (step port)^[3 * (S port).length + 4 * answer.length + 6]
        ⟨.seekWork, base S, wordTape answer⟩ =
      ⟨.done, base (Function.update S port answer), wordTape answer⟩ := by
  have he := erase_run S port (S port) (wordTape answer)
  simp only [Function.update_eq_self] at he
  have cleared : (step port)^[(2 * (S port).length + 1) + ((S port).length + 1)]
      ⟨.seekWork, base S, wordTape answer⟩ =
      ⟨.seekAnswer, base (Function.update S port []), wordTape answer⟩ := by
    rw [Function.iterate_add_apply, seek_work_run, he]
  have sought : (step port)^[ (answer.length + 1) +
      ((2 * (S port).length + 1) + ((S port).length + 1))]
      ⟨.seekWork, base S, wordTape answer⟩ =
      ⟨.loadLeft, base (Function.update S port []), cursor answer.reverse []⟩ := by
    rw [Function.iterate_add_apply, cleared]
    simpa only [cursor_nil, List.append_nil] using seek_answer_run port (base (Function.update S port [])) answer []
  have loaded : (step port)^[ (2 * answer.length + 2) + ((answer.length + 1) +
      ((2 * (S port).length + 1) + ((S port).length + 1)))]
      ⟨.seekWork, base S, wordTape answer⟩ =
      ⟨.back, (Tape.move .right)^[answer.length] (base (Function.update S port answer)), wordTape answer⟩ := by
    rw [Function.iterate_add_apply, sought]
    simpa only [List.length_nil, Function.iterate_zero_apply, List.length_reverse, List.reverse_reverse, List.append_nil] using
      load_run S port answer.reverse [] []
  have ht : 3 * (S port).length + 4 * answer.length + 6 =
      (answer.length + 1) + ((2 * answer.length + 2) + ((answer.length + 1) +
      ((2 * (S port).length + 1) + ((S port).length + 1)))) := by omega
  rw [ht, Function.iterate_add_apply, loaded, back_run]

/-- The loader starts from the actual packed source data. Old private contents
are erased by execution; they need not be empty. All other columns survive. -/
theorem run_packed {K Λ V : Type*} [DecidableEq K] [Fintype K]
    (src : TM2.Cfg (fun _ : K => Bool) Λ V) (port : K) (answer : List Bool) :
    (step port)^[3 * (src.stk port).length + 4 * answer.length + 6]
        ⟨.seekWork, (pack src).Tape, wordTape answer⟩ =
      ⟨.done, (pack {src with stk := Function.update src.stk port answer}).Tape,
        wordTape answer⟩ := run src.stk port answer

end ExplainableCrypto.Helios.Computational.OracleTapeInput
