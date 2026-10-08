import ExplainableCrypto.Helios.Computational.BitCopyMachine
import ExplainableCrypto.Helios.Computational.TM2StackFrame
import ExplainableCrypto.Helios.Computational.TM2MemoryFrame
import ExplainableCrypto.Helios.Computational.BitOracleMachine

/-! Realize oracle response-port replacement using the checked two-pass copy.
Clear the old destination first; outbound copying preserves its source, while
inbound movement consumes its private input. -/
namespace ExplainableCrypto.Helios.Computational.BitPortTransfer
open Turing.TM2
abbrev Stack := BitCopyMachine.Stack
open BitCopyMachine.Stack
inductive Label where
  | clear | copy (phase : Bool) | done
  deriving DecidableEq

instance : Fintype Label where
  elems := {.clear, .copy false, .copy true, .done}
  complete label := by cases label with
    | clear => simp
    | copy phase => cases phase <;> simp
    | done => simp

def program (consume : Bool) : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .clear => .pop destination (fun _ bit => bit) <| .branch Option.isSome
      (.goto (fun _ => .clear)) (.goto (fun _ => .copy false))
  | .copy phase => TM2ReturnLink.redirect Label.copy .done (BitCopyMachine.program phase)
  | .done => if consume then
      .pop source (fun _ bit => bit) <| .branch Option.isSome
        (.goto (fun _ => .done)) .halt
      else .halt

abbrev Config := Cfg (fun _ : Stack => Bool) Label (Option Bool)
def config (phase : Option Label) (word old scratchWord : List Bool) (v : Option Bool := none) : Config :=
  ⟨phase, v, (BitCopyMachine.config none word old scratchWord).stk⟩
abbrev tick (consume : Bool) := TM2ReturnLink.tick (program consume)

private theorem clear_step (consume : Bool) (word old scratchWord : List Bool) (v : Option Bool) :
    tick consume (config (some .clear) word old scratchWord v) = match old with
      | [] => config (some (.copy false)) word [] scratchWord
      | bit :: rest => config (some .clear) word rest scratchWord (some bit) := by
  cases old with
  | nil => simp [tick, TM2ReturnLink.tick, config, program, stepAux, BitCopyMachine.config]
  | cons bit rest =>
    simp [tick, TM2ReturnLink.tick, config, program, stepAux, BitCopyMachine.config]
    funext k
    cases k <;> simp

private theorem clear_run (consume : Bool) (word old scratchWord : List Bool) (v : Option Bool) :
    (tick consume)^[old.length + 1] (config (some .clear) word old scratchWord v) =
      config (some (.copy false)) word [] scratchWord := by
  induction old generalizing v with
  | nil => simp [clear_step]
  | cons bit rest ih =>
    rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, clear_step, ih]

private theorem before_done (consume : Bool) (word old : List Bool) (v : Option Bool) :
    ∃ fuel ≤ old.length + 2 * word.length + 3,
      (tick consume)^[fuel] (config (some .clear) word old [] v) =
        config (some .done) word word [] := by
  have copied := BitCopyMachine.run word [] none
  change (TM2ReturnLink.tick BitCopyMachine.program)^[2 * word.length + 2]
    (BitCopyMachine.config (some false) word [] []) = _ at copied
  simp only [List.append_nil] at copied
  obtain ⟨used, hu, he⟩ := TM2ReturnLink.run BitCopyMachine.program (program consume) Label.copy .done
    (fun _ => rfl) (2 * word.length + 2) (BitCopyMachine.config (some false) word [] [])
    (by rw [copied]; rfl)
  rw [copied] at he
  refine ⟨used + (old.length + 1), by omega, ?_⟩
  rw [Function.iterate_add_apply, clear_run]
  exact he

/-- Source-preserving replacement includes every end/return check. -/
theorem run (word old : List Bool) (v : Option Bool) :
    ∃ fuel ≤ old.length + 2 * word.length + 4,
      (tick false)^[fuel] (config (some .clear) word old [] v) = config none word word [] := by
  obtain ⟨used, hu, he⟩ := before_done false word old v
  refine ⟨used + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', he]
  rfl

private theorem cleanup_run (word value : List Bool) (v : Option Bool) :
    (tick true)^[word.length + 1] (config (some .done) word value [] v) =
      config none [] value [] := by
  induction word generalizing v with
  | nil => simp [tick, TM2ReturnLink.tick, config, program, stepAux, BitCopyMachine.config]
  | cons bit rest ih =>
    have hs : tick true (config (some .done) (bit :: rest) value [] v) =
        config (some .done) rest value [] (some bit) := by
      simp [tick, TM2ReturnLink.tick, config, program, stepAux, BitCopyMachine.config]
      funext k
      cases k <;> simp
    rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply, hs, ih]

/-- Consume the private answer after replacement, restoring empty private workspace. -/
theorem consume_run (word old : List Bool) (v : Option Bool) :
    ∃ fuel ≤ old.length + 3 * word.length + 4,
      (tick true)^[fuel] (config (some .clear) word old [] v) = config none [] word [] := by
  obtain ⟨used, hu, he⟩ := before_done true word old v
  refine ⟨word.length + 1 + used, by omega, ?_⟩
  rw [Function.iterate_add_apply, he, cleanup_run]

/-- The old append-copy theorem cannot realize a nonempty destination replacement. -/
theorem append_is_not_replacement :
    let out := BitCopyMachine.tick^[6]
      (BitCopyMachine.config (some false) [true, false] [true] [])
    out.stk destination = [true, false, true] ∧ out.stk destination ≠ [true, false] := by
  decide +kernel

end ExplainableCrypto.Helios.Computational.BitPortTransfer
