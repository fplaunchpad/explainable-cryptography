import ExplainableCrypto.Helios.Computational.BinarySubtractMachine
import ExplainableCrypto.Helios.Computational.TM2StackFrame

/-! Complete binary remainder by actual stack execution. The existing guarded
subtraction is linked as a subroutine; neither the driver nor its transitions
use host division, modulo, list reversal or conversion to natural numbers. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModuloMachine
open Turing.TM2
abbrev CoreStack := BinarySubtractMachine.Stack
abbrev CoreLabel := BinarySubtractMachine.Label
abbrev Stack := CoreStack ⊕ Bool

inductive Label where
  | reverseInput | read | toTemp | toLeft | call (label : CoreLabel)
  deriving DecidableEq
open Label
instance : Inhabited Label := ⟨reverseInput⟩
instance : Fintype Label where
  elems := Finset.univ.image call ∪ {reverseInput,read,toTemp,toLeft}
  complete l := by cases l <;> simp

abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
private def frame (raw pending : List Bool) : Bool → List Bool
  | false => raw | true => pending
private def localProgram (l : CoreLabel) : Stmt (fun _ : Stack => Bool) CoreLabel (Option Bool) :=
  TM2StackFrame.relocate (Equiv.refl Stack) (BinarySubtractMachine.program l)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | call l => TM2ReturnLink.redirect call toTemp (localProgram l)
  | reverseInput => .pop (.inr false) (fun _ b => b) <| .branch Option.isSome
      (.push (.inr true) (fun b => b.getD false) (.goto (fun _ => reverseInput)))
      (.load (fun _ => none) (.goto (fun _ => read)))
  | Label.read => .pop (.inr true) (fun _ b => b) <| .branch Option.isSome
      (.branch (fun b => b.getD false)
        (.load (fun _ => none) (.goto (fun _ => call (.shift true))))
        (.load (fun _ => none) (.goto (fun _ => call (.shift false)))))
      (.load (fun _ => none) .halt)
  | toTemp => .pop (.inl .out) (fun _ b => b) <| .branch Option.isSome
      (.push (.inl .savedLeft) (fun b => b.getD false) (.goto (fun _ => toTemp)))
      (.goto (fun _ => toLeft))
  | toLeft => .pop (.inl .savedLeft) (fun _ b => b) <| .branch Option.isSome
      (.push (.inl .left) (fun b => b.getD false) (.goto (fun _ => toLeft)))
      (.load (fun _ => none) (.goto (fun _ => read)))

def tick : Config → Config := TM2ReturnLink.tick program

/-- Driver boundary state; the subtraction difference/right archive are empty. -/
def state (phase : Option Label) (x y result archive raw pending : List Bool)
    (v : Option Bool := none) : Config :=
  ⟨phase,v,TM2StackFrame.data (Equiv.refl Stack)
    (BinarySubtractMachine.state none x y [] archive [] result v).stk (frame raw pending)⟩

theorem supports : Supports program Finset.univ := by
  have h : ∀ s : Stmt (fun _ : Stack => Bool) Label (Option Bool),
      SupportsStmt Finset.univ s := by
    intro s
    induction s <;> simp_all [SupportsStmt]
  exact ⟨by simp, fun l _ => h (program l)⟩

private theorem call_run (r q : Nat) (b : Bool) (hr : r < q) (raw pending : List Bool) :
    ∃ u ≤ 6*q.size+9,
      tick^[u] (state (some (call (.shift b))) r.bits q.bits [] [] raw pending) =
        state (some toTemp) [] q.bits ((Nat.bit b r)%q).bits [] raw pending
          (some (decide (q ≤ Nat.bit b r))) := by
  obtain ⟨u,hu,he⟩ := BinarySubtractMachine.remainder_step r q b hr
  let c := BinarySubtractMachine.state (some (.shift b)) r.bits q.bits [] [] [] []
  have hs := TM2StackFrame.run (Equiv.refl Stack) BinarySubtractMachine.program u c (frame raw pending)
  change (TM2ReturnLink.tick localProgram)^[u]
    (TM2StackFrame.embed (Equiv.refl Stack) c (frame raw pending)) = _ at hs
  change (TM2ReturnLink.tick BinarySubtractMachine.program)^[u] c = _ at he
  rw [he] at hs
  obtain ⟨used,hused,husedRun⟩ := TM2ReturnLink.run localProgram program call toTemp
    (fun _ => rfl) u (TM2StackFrame.embed (Equiv.refl Stack) c (frame raw pending))
    (by rw [hs]; rfl)
  rw [hs] at husedRun
  exact ⟨used,hused.trans hu,husedRun⟩

private theorem reverse_input_run (x y raw pending : List Bool) (v : Option Bool) :
    tick^[raw.length+1] (state (some reverseInput) x y [] [] raw pending v) =
      state (some read) x y [] [] [] (raw.reverse++pending) := by
  induction raw generalizing pending v with
  | nil =>
    simp [tick, TM2ReturnLink.tick, state, program, frame, TM2StackFrame.data]
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr b => cases b <;> rfl
  | cons b raw ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : tick (state (some reverseInput) x y [] [] (b::raw) pending v) =
        state (some reverseInput) x y [] [] raw (b::pending) (some b) := by
      simp [tick, TM2ReturnLink.tick, state, program, frame, TM2StackFrame.data]
      funext k
      cases k with
      | inl k => cases k <;> rfl
      | inr b => cases b <;> rfl
    rw [hs,ih]
    simp

private theorem to_temp_run (x y result archive raw pending : List Bool) (v : Option Bool) :
    tick^[result.length+1] (state (some toTemp) x y result archive raw pending v) =
      state (some toLeft) x y [] (result.reverse++archive) raw pending := by
  induction result generalizing archive v with
  | nil => simp [tick, TM2ReturnLink.tick, state, program, TM2StackFrame.data,
      BinarySubtractMachine.state]
  | cons b result ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : tick (state (some toTemp) x y (b::result) archive raw pending v) =
        state (some toTemp) x y result (b::archive) raw pending (some b) := by
      simp [tick, TM2ReturnLink.tick, state, program, TM2StackFrame.data,
        BinarySubtractMachine.state]
      funext k
      cases k with
      | inl k => cases k <;> rfl
      | inr b => cases b <;> rfl
    rw [hs,ih]
    simp

private theorem to_left_run (x y archive raw pending : List Bool) (v : Option Bool) :
    tick^[archive.length+1] (state (some toLeft) x y [] archive raw pending v) =
      state (some read) (archive.reverse++x) y [] [] raw pending := by
  induction archive generalizing x v with
  | nil => simp [tick, TM2ReturnLink.tick, state, program, TM2StackFrame.data,
      BinarySubtractMachine.state]
  | cons b archive ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have hs : tick (state (some toLeft) x y [] (b::archive) raw pending v) =
        state (some toLeft) (b::x) y [] archive raw pending (some b) := by
      simp [tick, TM2ReturnLink.tick, state, program, TM2StackFrame.data,
        BinarySubtractMachine.state]
      funext k
      cases k with
      | inl k => cases k <;> rfl
      | inr b => cases b <;> rfl
    rw [hs,ih]
    simp

private theorem read_step (x y raw pending : List Bool) (b : Bool) :
    tick (state (some read) x y [] [] raw (b::pending)) =
      state (some (call (.shift b))) x y [] [] raw pending := by
  cases b <;> simp [tick, TM2ReturnLink.tick, state, program, frame, TM2StackFrame.data]
  all_goals
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr b => cases b <;> rfl

private def value (r : Nat) (word : List Bool) : Nat :=
  word.foldl (fun r b => Nat.bit b r) r

private theorem bit_mod (q r : Nat) (b : Bool) :
    (Nat.bit b (r%q))%q = (Nat.bit b r)%q := by
  simp [Nat.bit_val, Nat.add_mod, Nat.mul_mod]

private theorem value_mod (q r : Nat) (word : List Bool) :
    value (r%q) word % q = value r word % q := by
  induction word generalizing r with
  | nil => simp [value]
  | cons b word ih =>
    change value (Nat.bit b (r%q)) word % q = value (Nat.bit b r) word % q
    rw [← ih (Nat.bit b (r%q)), bit_mod, ih]

private theorem loop (q r : Nat) (hr : r < q) (raw pending : List Bool) :
    ∃ fuel ≤ pending.length*(8*q.size+12)+1,
      tick^[fuel] (state (some read) r.bits q.bits [] [] raw pending) =
        state none (value r pending % q).bits q.bits [] [] raw [] := by
  induction pending generalizing r with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simp [value, Nat.mod_eq_of_lt hr, tick, TM2ReturnLink.tick, state, program,
      frame, TM2StackFrame.data]
  | cons b pending ih =>
    let next := (Nat.bit b r)%q
    have hnext : next < q := Nat.mod_lt _ (by omega)
    obtain ⟨u,hu,hcall⟩ := call_run r q b hr raw pending
    obtain ⟨v,hv,hrest⟩ := ih next hnext
    have hwidth : next.bits.length ≤ q.size := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le_size hnext.le
    let back := (next.bits.reverse.length+1)+(next.bits.length+1)
    have hback : tick^[back]
        (state (some toTemp) [] q.bits next.bits [] raw pending
          (some (decide (q ≤ Nat.bit b r)))) =
        state (some read) next.bits q.bits [] [] raw pending := by
      rw [show back = (next.bits.reverse.length+1)+(next.bits.length+1) from rfl,
        Function.iterate_add_apply, to_temp_run]
      simp only [List.append_nil]
      rw [to_left_run]
      simp
    refine ⟨v+(back+(u+1)),?_,?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      dsimp only [back]
      simp only [List.length_reverse]
      omega
    · rw [Function.iterate_add_apply tick v, Function.iterate_add_apply tick back,
        Function.iterate_succ_apply, read_step, hcall, hback, hrest]
      rw [show value next pending % q = value (Nat.bit b r) pending % q from
        value_mod q (Nat.bit b r) pending]
      rfl

/-- Full loaded-word division: input is little-endian, including arbitrary high
zero padding. All reversal, calls, return transfers and halt are executed.
The canonical modulus is retained; input and all scratch stacks are cleared. -/
theorem run (word : List Bool) (q : Nat) (hq : 0 < q) :
    ∃ fuel ≤ word.length*(8*q.size+13)+2,
      tick^[fuel] (state (some reverseInput) [] q.bits [] [] word []) =
        state none (bitsValue word % q).bits q.bits [] [] [] [] := by
  obtain ⟨u,hu,he⟩ := loop q 0 hq [] word.reverse
  refine ⟨u+(word.length+1),?_,?_⟩
  · simp only [List.length_reverse] at hu
    have hm : word.length*(8*q.size+13) = word.length*(8*q.size+12)+word.length := by
      simpa [Nat.add_assoc] using Nat.mul_succ word.length (8*q.size+12)
    omega
  · rw [Function.iterate_add_apply, reverse_input_run]
    simpa [value, List.foldl_reverse, bitsValue] using he

/-- The result's bit width is bounded by the retained modulus width, for every
raw word. The same invariant bounds each linked remainder and return transfer. -/
theorem result_width (word : List Bool) (q : Nat) (hq : 0 < q) :
    (bitsValue word % q).bits.length ≤ q.size := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le_size (Nat.mod_lt _ hq).le

end ExplainableCrypto.Helios.Computational.BinaryModuloMachine
