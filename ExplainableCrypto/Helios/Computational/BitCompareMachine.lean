import Mathlib.Computability.TuringMachine.StackTuringMachine
import ExplainableCrypto.Helios.Computational.BallotCacheBitSize

/-! Concrete finite-control bit comparison for the encoded hash-key lookup.
The bound counts actual Mathlib TM2 transitions, not arbitrary Lean callbacks.
Whole-cache execution and quantitative lowering to TM0 remain separate. -/
namespace ExplainableCrypto.Helios.Computational
namespace BitCompareMachine

open Turing.TM2

abbrev Memory := Option Bool × Option Bool
abbrev Config := Cfg (fun _ : Bool => Bool) Unit Memory

def program : Unit → Stmt (fun _ : Bool => Bool) Unit Memory := fun _ =>
  .pop false (fun v b => (b,v.2)) <|
  .pop true (fun v b => (v.1,b)) <|
  .branch (fun v => decide (v.1 = v.2) && v.1.isSome)
    (.goto (fun _ => ())) .halt

def start (xs ys : List Bool) (v : Memory := (none,none)) : Config :=
  ⟨some (),v,fun k => if k then ys else xs⟩

/-- Halted configurations remain fixed so a stated upper bound is usable as fuel. -/
def tick (c : Config) : Config := (step program c).getD c

def answer (c : Config) : Bool := decide (c.var.1 = c.var.2)

/-- Only one label, two binary stacks and nine possible local states are used. -/
theorem supports : Supports program Finset.univ := by
  simp [Supports,SupportsStmt,program]

private theorem halted_tick (c : Config) (h : c.l = none) : tick c = c := by
  rcases c with ⟨l,v,s⟩
  cases h
  rfl

private theorem halted_iterate (c : Config) (h : c.l = none) (n : Nat) :
    tick^[n] c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,halted_tick c h]

private theorem step_start (xs ys : List Bool) (v : Memory) :
    tick (start xs ys v) =
      ⟨if decide (xs.head? = ys.head?) && xs.head?.isSome then some () else none,
        (xs.head?,ys.head?), fun k => if k then ys.tail else xs.tail⟩ := by
  have hs : Function.update (Function.update (fun k : Bool => if k then ys else xs)
      false xs.tail) true ys.tail = (fun k => if k then ys.tail else xs.tail) := by
    funext k
    cases k <;> simp
  simp [tick,start,step,program,stepAux,hs,Bool.cond_eq_ite]
  split <;> rfl

/-- A complete concrete execution halts with exact word equality, on all words.
The finite input memory is irrelevant; it cannot supply an equality oracle. -/
theorem run (xs ys : List Bool) (v : Memory) :
    let out := tick^[xs.length+1] (start xs ys v)
    out.l = none ∧ answer out = decide (xs = ys) := by
  induction xs generalizing ys v with
  | nil =>
    cases ys <;> simp [step_start,answer]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply]
      rw [step_start]
      simp only [List.head?_cons,List.head?_nil,List.tail_cons,List.tail_nil,
        reduceCtorEq,decide_false,Bool.false_and,Bool.false_eq_true,↓reduceIte]
      rw [halted_iterate _ rfl]
      simp [answer]
    | cons b ys =>
      by_cases hab : a = b
      · subst b
        rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply,step_start]
        simpa only [List.head?_cons,List.tail_cons,decide_true,Bool.true_and,
          Option.isSome_some,↓reduceIte,List.cons.injEq,true_and,start]
          using ih ys (some a,some a)
      · rw [List.length_cons, Nat.add_assoc, Function.iterate_succ_apply]
        rw [step_start]
        simp only [List.head?_cons,List.tail_cons,Option.some.injEq,hab,decide_false,
          Bool.false_and,Bool.false_eq_true,↓reduceIte]
        rw [halted_iterate _ rfl]
        simp [answer,hab]

/-- Original complete-key equality, computed by the concrete machine on its
already-loaded canonical input words. The fuel bound is derived from the actual
key record; encoding, loading and the enclosing lookup are not charged here. -/
theorem key_run {p q : Nat} [NeZero p] [NeZero q]
    (a b : BallotForkPoint (PrimeGroup p q)) :
    ∃ n ≤ keyRecordBitBound p + 1,
      let out := tick^[n] (start ((ballotKeyBitCodec p q).encode a)
        ((ballotKeyBitCodec p q).encode b))
      out.l = none ∧ answer out = decide (a = b) := by
  have h := run ((ballotKeyBitCodec p q).encode a)
    ((ballotKeyBitCodec p q).encode b) (none,none)
  refine ⟨_,Nat.add_le_add_right (ballotKeyBits_length_le a) 1,h.1,?_⟩
  simpa only [(BitRecordCodec.injective (ballotKeyBitCodec p q)).eq_iff] using h.2

theorem memory_card : Fintype.card Memory = 9 := by decide

/-- Equal nonempty words consume the matching heads and terminate at the end. -/
theorem equal_control :
    let out := tick^[4] (start [true,false,true] [true,false,true])
    out.l = none ∧ answer out = true := by decide

/-- A differing third bit must not be lost after the matching prefix. -/
theorem mismatch_control :
    let out := tick^[4] (start [true,false,true] [true,false,false])
    out.l = none ∧ answer out = false := by decide

/-- Neither ordering of a strict prefix is accepted as equality. -/
theorem prefix_control :
    answer (tick^[2] (start [true] [true,false])) = false ∧
    answer (tick^[3] (start [true,false] [true])) = false := by decide

/-- Matching heads cause another actual transition, rather than immediate halt. -/
theorem matching_head_continues :
    (tick (start [true,false] [true,false])).l = some () := by decide

#print axioms supports
#print axioms run
#print axioms key_run
#print axioms memory_card
#print axioms equal_control
#print axioms mismatch_control
#print axioms prefix_control
#print axioms matching_head_continues
end BitCompareMachine
end ExplainableCrypto.Helios.Computational
