import ExplainableCrypto.Helios.Computational.BinaryModuloMachine

/-! Concrete complete-state executions, including nonpalindromic input/output,
zero and unit moduli boundaries, and a live startup prefix. -/
namespace ExplainableCrypto.Helios.Computational.BinaryModuloMachineControls
open BinaryModuloMachine

private def observe (c : Config) : Option Label × Option Bool × List (List Bool) :=
  (c.l,c.var,[c.stk (.inl .left), c.stk (.inl .right), c.stk (.inl .diff),
    c.stk (.inl .savedLeft), c.stk (.inl .savedRight), c.stk (.inl .out),
    c.stk (.inr false), c.stk (.inr true)])

/-- Input six modulo five returns one; reading the input backward returns three. -/
theorem input_order :
    observe (tick^[200] (state (some .reverseInput) [] [true,false,true] [] []
      [false,true,true] [])) =
      (none,none,[[true],[true,false,true],[],[],[],[],[],[]]) := by decide +kernel

/-- Input two modulo three retains nonpalindromic output two, excluding a
one-pass transfer that would reverse the result to one. -/
theorem return_order :
    observe (tick^[100] (state (some .reverseInput) [] [true,true] [] [] [false,true] [])) =
      (none,none,[[false,true],[true,true],[],[],[],[],[],[]]) := by decide +kernel

/-- Leading high zeros do not change the result, and all eight stacks are checked. -/
theorem padded_input :
    observe (tick^[200] (state (some .reverseInput) [] [true,false,true] [] []
      [false,true,true,false,false] [])) =
      (none,none,[[true],[true,false,true],[],[],[],[],[],[]]) := by decide +kernel

/-- The minimum positive modulus yields canonical zero after nonzero input. -/
theorem modulus_one :
    observe (tick^[100] (state (some .reverseInput) [] [true] [] [] [true,false,true] [])) =
      (none,none,[[],[true],[],[],[],[],[],[]]) := by decide +kernel

/-- Empty input executes reversal termination and read termination, rather
than getting stuck before entering the loop. -/
theorem empty_input :
    observe (tick^[2] (state (some .reverseInput) [] [true,true] [] [] [] [])) =
      (none,none,[[],[true,true],[],[],[],[],[],[]]) := by decide +kernel

/-- After the first startup move the machine is live, and has moved exactly
one raw digit to the pending input stack. -/
theorem live_prefix :
    observe (tick (state (some .reverseInput) [] [true,true] [] [] [false,true] [])) =
      (some .reverseInput,some false,[[],[true,true],[],[],[],[],[true],[false]]) := by
  decide +kernel

/-- The general theorem covers an arbitrary raw word, not just the literal
executions above; modulus three gives the derived linear clock 29*N+2. -/
theorem all_words_mod_three (word : List Bool) :
    ∃ fuel ≤ word.length*29+2,
      tick^[fuel] (state (some .reverseInput) [] [true,true] [] [] word []) =
        state none (bitsValue word % 3).bits [true,true] [] [] [] [] := by
  simpa [show Nat.size 3 = 2 from rfl, show Nat.bits 3 = [true,true] from rfl] using
    run word 3 (by decide)

end ExplainableCrypto.Helios.Computational.BinaryModuloMachineControls
