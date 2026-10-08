import ExplainableCrypto.Helios.Computational.TM2TapeRuns

/-! A head-local two-tape outgoing transfer. Each transition reads current
cells, writes at most one query cell and moves each head by at most one.
The four control states contain no unbounded values or host callbacks. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeOutput
open Turing TM2to1 TM2TapeRuns

inductive Phase where
  | clear | copy | back | done
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.clear, .copy, .back, .done}, by intro p; cases p <;> simp⟩

abbrev WorkTape (K : Type*) := Tape (TM2to1.Γ' K (fun _ => Bool))

structure Config (K : Type*) where
  phase : Phase
  work : WorkTape K
  query : Tape (Option Bool)

/-- The ordinary top-first raw word on a native query tape, head at its beginning. -/
def wordTape (word : List Bool) : Tape (Option Bool) :=
  Tape.mk' ∅ (ListBlank.mk (word.map some))

private def parked (word : List Bool) : Tape (Option Bool) :=
  Tape.mk' ∅ (ListBlank.mk (none :: word.map some))

/-- Query writing proceeds leftward while the reversed work column is read
rightward. No transition traverses a list or changes the work tape cells. -/
def step {K : Type*} (port : K) (c : Config K) : Config K :=
  match c.phase with
  | .clear => match c.query.head with
    | some _ => ⟨.clear, c.work, (c.query.write none).move .right⟩
    | none => ⟨.copy, c.work, c.query⟩
  | .copy => match c.work.head.2 port with
    | some bit => ⟨.copy, c.work.move .right, (c.query.write (some bit)).move .left⟩
    | none => ⟨.back, c.work, c.query.move .right⟩
  | .back => if c.work.head.1 then ⟨.done, c.work, c.query⟩
      else ⟨.back, c.work.move .left, c.query⟩
  | .done => c

private theorem write_parked (word : List Bool) (bit : Bool) :
    ((parked word).write (some bit)).move .left = parked (bit :: word) := rfl

private theorem blank_cons : ListBlank.cons (none : Option Bool) ∅ = ∅ := by
  apply ListBlank.ext
  intro n
  cases n <;> rfl

private theorem unpark (word : List Bool) :
    (parked word).move .right = wordTape word := by
  simp [parked, wordTape, Tape.move_right_mk', blank_cons]

private theorem clear_bit (bit : Bool) (word : List Bool) :
    ((wordTape (bit :: word)).write none).move .right = wordTape word := by
  simp [wordTape, Tape.write_mk', Tape.move_right_mk', blank_cons]

private theorem clear_prefix {K : Type*} (port : K) (work : WorkTape K)
    (word : List Bool) :
    (step port)^[word.length] ⟨.clear, work, wordTape word⟩ =
      ⟨.clear, work, wordTape []⟩ := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : step port ⟨.clear, work, wordTape (bit :: word)⟩ =
        ⟨.clear, work, wordTape word⟩ := by
      change (⟨.clear, work, ((wordTape (bit :: word)).write none).move .right⟩ : Config K) = _
      rw [clear_bit]
    rw [hs, ih]

/-- Physically clear the previous canonical query word; blank restoration is
 derived rather than assumed afresh at each outgoing transfer. -/
theorem clear_run {K : Type*} (port : K) (work : WorkTape K) (word : List Bool) :
    (step port)^[word.length + 1] ⟨.clear, work, wordTape word⟩ =
      ⟨.copy, work, wordTape []⟩ := by
  rw [Function.iterate_succ_apply', clear_prefix]
  rfl

private theorem copy_prefix {K : Type*} (port : K) (work : WorkTape K)
    (word : List Bool) (hread : ∀ i,
      ((Tape.move .right)^[i] work).head.2 port = word.reverse[i]?)
    (n : Nat) (hn : n ≤ word.length) :
    (step port)^[n] ⟨.copy, work, wordTape []⟩ =
      ⟨.copy, (Tape.move .right)^[n] work, parked ((word.reverse.take n).reverse)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hn' : n < word.reverse.length := by simpa using Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    simp only [step, hread n, List.getElem?_eq_getElem hn']
    rw [write_parked, List.take_succ_eq_append_getElem hn', List.reverse_append]
    rw [Function.iterate_succ_apply']
    rfl

private theorem return_scan {K : Type*} (port : K) (work : WorkTape K)
    (query : Tape (Option Bool)) (hmark : ∀ i,
      ((Tape.move .right)^[i] work).head.1 = (i == 0)) (n : Nat) :
    (step port)^[n + 1] ⟨.back, (Tape.move .right)^[n] work, query⟩ =
      ⟨.done, work, query⟩ := by
  induction n with
  | zero =>
    have hz : work.head.1 = true := hmark 0
    simp [step, hz]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hs : step port ⟨.back, (Tape.move .right)^[n + 1] work, query⟩ =
        ⟨.back, (Tape.move .right)^[n] work, query⟩ := by
      simp only [step, hmark (n + 1), beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte]
      rw [Function.iterate_succ_apply', Tape.move_right_left]
    rw [hs, ih]

/-- Exact transfer for a tape with the specified selected column and bottom
marker. The whole work tape, including all other columns, is restored. -/
theorem run {K : Type*} (port : K) (work : WorkTape K) (word : List Bool)
    (hread : ∀ i, ((Tape.move .right)^[i] work).head.2 port = word.reverse[i]?)
    (hmark : ∀ i, ((Tape.move .right)^[i] work).head.1 = (i == 0)) :
    (step port)^[2 * word.length + 2] ⟨.copy, work, wordTape []⟩ =
      ⟨.done, work, wordTape word⟩ := by
  have hp := copy_prefix port work word hread word.length le_rfl
  have ht : word.reverse.take word.length = word.reverse := List.take_of_length_le (by simp)
  simp only [ht, List.reverse_reverse] at hp
  have he : step port ⟨.copy, (Tape.move .right)^[word.length] work, parked word⟩ =
      ⟨.back, (Tape.move .right)^[word.length] work, wordTape word⟩ := by
    simp only [step, hread, List.getElem?_eq_none (by simp : word.reverse.length ≤ word.length)]
    rw [unpark]
  have issued : (step port)^[word.length + 1] ⟨.copy, work, wordTape []⟩ =
      ⟨.back, (Tape.move .right)^[word.length] work, wordTape word⟩ := by
    rw [Function.iterate_succ_apply', hp, he]
  have eq : 2 * word.length + 2 = (word.length + 1) + (word.length + 1) := by omega
  rw [eq, Function.iterate_add_apply, issued, return_scan port work _ hmark]

/-- Every actual packed source configuration supplies the required column and
marker laws. No tape-presentation certificate is supplied by the caller. -/
theorem run_packed {K Λ V : Type*} [DecidableEq K] [Fintype K]
    (src : TM2.Cfg (fun _ : K => Bool) Λ V) (port : K) :
    (step port)^[2 * (src.stk port).length + 2]
        ⟨.copy, (pack src).Tape, wordTape []⟩ =
      ⟨.done, (pack src).Tape, wordTape (src.stk port)⟩ := by
  apply run
  · intro i
    simp only [pack, Tape.move_right_n_head, Tape.mk'_nth_nat,
      addBottom_nth_snd, columns_nth]
  · intro i
    cases i with
    | zero => rfl
    | succ i =>
      change ((Tape.move .right)^[i + 1]
        (Tape.mk' ∅ (addBottom (columns src.stk)))).head.1 = false
      rw [Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst]

/-- Replace a prior native query by the actual selected source word. Both
cleanup and export are executed, including empty and shorter replacements. -/
theorem run_replacing {K Λ V : Type*} [DecidableEq K] [Fintype K]
    (src : TM2.Cfg (fun _ : K => Bool) Λ V) (port : K) (previous : List Bool) :
    (step port)^[previous.length + 2 * (src.stk port).length + 3]
        ⟨.clear, (pack src).Tape, wordTape previous⟩ =
      ⟨.done, (pack src).Tape, wordTape (src.stk port)⟩ := by
  have ht : previous.length + 2 * (src.stk port).length + 3 =
      (2 * (src.stk port).length + 2) + (previous.length + 1) := by omega
  rw [ht, Function.iterate_add_apply, clear_run, run_packed]

end ExplainableCrypto.Helios.Computational.OracleTapeOutput
