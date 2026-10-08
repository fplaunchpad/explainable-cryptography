import ExplainableCrypto.Helios.Computational.OracleTapeOutput
import ExplainableCrypto.Helios.Computational.BitOracleMachine

/-! Native oracle semantics for explicit query/answer tapes. The query decoder
belongs to the native event, not to the local machine instruction set. -/
namespace ExplainableCrypto.Helios.Computational.OracleTapeDispatch
open Turing OracleTapeOutput OracleComp OracleSpec

private def readPrefix : List (Option Bool) → List Bool
  | [] | none :: _ => []
  | some bit :: rest => bit :: readPrefix rest

private theorem prefix_blanks (xs : List (Option Bool)) (n : Nat) :
    readPrefix (xs ++ List.replicate n none) = readPrefix xs := by
  induction xs with
  | nil => cases n <;> rfl
  | cons b xs ih => cases b <;> simp [readPrefix, ih]

/-- Native interpretation reads the contiguous word beginning at the head.
Blank extension of a half-tape does not change this native word. -/
def readWord (tape : Tape (Option Bool)) : List Bool :=
  tape.right₀.liftOn readPrefix (by
    rintro xs ys ⟨n, rfl⟩
    exact (prefix_blanks xs n).symm)

/-- Every ordinary raw word is retained exactly, including the empty word. -/
theorem read_wordTape (word : List Bool) : readWord (wordTape word) = word := by
  unfold readWord wordTape
  rw [Tape.mk'_right₀]
  change readPrefix (word.map some) = word
  induction word with
  | nil => rfl
  | cons bit word ih => simpa only [List.map, readPrefix] using congrArg (List.cons bit) ih

inductive Kind where
  | hash | coin
  deriving DecidableEq

structure Tapes (K : Type) where
  work : WorkTape K
  query : Tape (Option Bool)
  answer : Tape (Option Bool)

/-- Only a native event reads a complete query or writes a complete reply.
The native interface retains the work/query tapes and replaces the answer tape. -/
def dispatch {K : Type} (kind : Kind) (tapes : Tapes K) :
    OracleComp BitOracleMachine.spec (Tapes K) := do
  let answer : List Bool ← match kind with
    | .hash => liftM (BitOracleMachine.spec.query (.hash (readWord tapes.query)))
    | .coin => (fun bit => [bit]) <$> liftM (BitOracleMachine.spec.query .coin)
  pure {tapes with answer := wordTape answer}

/-- The native event on a canonical query is exactly the original raw hash call. -/
theorem hash_word {K : Type} (work : WorkTape K) (word : List Bool)
    (oldAnswer : Tape (Option Bool)) :
    dispatch .hash ⟨work, wordTape word, oldAnswer⟩ =
      (do let answer ← liftM (BitOracleMachine.spec.query (.hash word))
          pure (⟨work, wordTape word, wordTape answer⟩ : Tapes K)) := by
  unfold dispatch
  rw [read_wordTape]
  rfl

/-- Coin delivery writes the actual returned bit as a one-bit native word. -/
theorem coin_word {K : Type} (tapes : Tapes K) :
    dispatch .coin tapes =
      (do let bit ← liftM (BitOracleMachine.spec.query .coin)
          pure {tapes with answer := wordTape [bit]}) := by
  simp only [dispatch, map_eq_bind_pure_comp, bind_assoc]
  rfl

end ExplainableCrypto.Helios.Computational.OracleTapeDispatch
