import ExplainableCrypto.Helios.Computational.PrimeNoncePairMachineRun

/-! Independently calculated full pair traces and executed caller mutations.
Saved context is private machine data, not an added protocol observation. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNoncePairControls
open OracleComp OracleSpec BitOracleMachine PrimeNoncePairMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 32768

private def handler : QueryImpl spec (StateT (List Bool) Id) := fun r tape =>
  match r with
  | .coin => (tape.headD false,tape.tail)
  | .hash word => (word,tape)

def trace (slack q : Nat) (context tape : List Bool) : Config 11 size 3 × List Bool :=
  (simulateQ handler (Prod.fst <$> run code (clock slack q)
    (start (SamplerOperands.input slack q []) context))).run tape

private theorem trace_eq (slack q : Nat) (hq : 2 ≤ q) (context tape : List Bool) :
    trace slack q context tape = (simulateQ handler (do
      let a ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
      let b ← CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
      pure (result (SamplerOperands.input slack q [])
        (uniformNatEncode (bitsValue a % (q-1)+1))
        (uniformNatEncode (bitsValue b % (q-1)+1)) (q-1).bits context))).run tape := by
  obtain ⟨charge,_,h⟩ := pair_run slack q hq context
  unfold trace
  rw [h]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

private def contextWord : List Bool := [true,false,true,true,false]
private def firstLowTape : List Bool := [false,false,false,true,true,true,true,false,true]
private def firstHighTape : List Bool := [true,true,true,false,false,false,true,false,true]

/-- At q=5, first coins 000 give one and following coins 111 give four.
The whole result retains public record8, first nonce9, context10 and suffix101. -/
theorem low_high_control : trace 0 5 contextWord firstLowTape =
    ((⟨none,2,![[],[false,false,true],[],[],[],[true,true,true,false,false,false,true],[],[],
      [false,true,true,true,false,true,false,true],[true,false,true],
      [true,false,true,true,false]]⟩ : Config 11 size 3),[true,false,true]) := by
  rw [trace_eq 0 5 (by decide)]
  rfl

/-- Reversing the two extreme coin words reverses the independently stored
nonces while preserving exactly the same residual stream and saved data. -/
theorem high_low_control : trace 0 5 contextWord firstHighTape =
    ((⟨none,2,![[],[false,false,true],[],[],[],[true,false,true],[],[],
      [false,true,true,true,false,true,false,true],[true,true,true,false,false,false,true],
      [true,false,true,true,false]]⟩ : Config 11 size 3),[true,false,true]) := by
  rw [trace_eq 0 5 (by decide)]
  rfl

/-- The singleton q=2 range still executes two draws, consuming two coins. -/
theorem singleton_control : trace 0 2 contextWord [false,true,true,false] =
    ((⟨none,2,![[],[true],[],[],[],[true,false,true],[],[],
      [false,true,true,false,false,true],[true,false,true],
      [true,false,true,true,false]]⟩ : Config 11 size 3),[true,false]) := by
  rw [trace_eq 0 2 (by decide)]
  rfl

/-- A caller that copies the first answer into both positions cannot explain
the checked q=5 trace. -/
theorem second_not_first :
    (trace 0 5 contextWord firstLowTape).1.stk 5 ≠
      (trace 0 5 contextWord firstLowTape).1.stk 9 := by
  rw [low_high_control]
  decide +kernel

/-- Correct output requires consumption of both words, not only the first. -/
theorem both_words_consumed :
    (trace 0 5 contextWord firstLowTape).2 ≠ [true,true,true,true,false,true] := by
  rw [low_high_control]
  decide +kernel

private def mutated (m : Nat) (l : Fin size) : Command 11 size 3 :=
  if m == 1 && l == 0 then .compute .halt
  else if m == 2 && l == 0 then
    match code l with
    | .compute s => .compute (.push 10 (fun _ => false) s)
    | other => other
  else if m == 3 && l.val >= (secondLabel 0).val then
    match code l with
    | .coin dest next => .compute (.push dest (fun _ => false) (.goto (fun _ => next)))
    | other => other
  else if m == 4 && l == 0 then .compute
    (.load (fun _ => 0) (.goto (fun _ => secondLabel 0)))
  else code l

private def mutantReadout (m : Nat) :=
  let out := (simulateQ handler (Prod.fst <$> run (mutated m) 400
    (start (SamplerOperands.input 0 5 []) []))).run firstLowTape
  (out.1.var.val,out.1.stk 5,out.1.stk 9,out.1.stk 10,out.2)

/-- Halting at the first return leaves the first answer unsaved and the second
coin word untouched. -/
theorem omitted_second_counterexample : mutantReadout 1 =
    (2,[true,false,true],[],[],[true,true,true,true,false,true]) := by decide +kernel

/-- A write into context10 corrupts saved data despite both correct nonces. -/
theorem corrupted_context_counterexample : mutantReadout 2 =
    (2,[true,true,true,false,false,false,true],[true,false,true],[false],[true,false,true]) := by
  decide +kernel

/-- Substituting zero bits for actual second coin queries duplicates nonce one
and retains the entire second coin word in the residual stream. -/
theorem fixed_second_coins_counterexample : mutantReadout 3 =
    (2,[true,false,true],[true,false,true],[],[true,true,true,true,false,true]) := by
  decide +kernel

/-- Direct sampler reentry without reload/cleanup rejects with memory one,
leaves the first nonce unsaved and consumes no second coin word. -/
theorem omitted_reentry_counterexample : mutantReadout 4 =
    (1,[true,false,true],[],[],[true,true,true,true,false,true]) := by decide +kernel

#print axioms low_high_control
#print axioms high_low_control
#print axioms singleton_control
#print axioms second_not_first
#print axioms both_words_consumed
#print axioms omitted_second_counterexample
#print axioms corrupted_context_counterexample
#print axioms fixed_second_coins_counterexample
#print axioms omitted_reentry_counterexample
end ExplainableCrypto.Helios.Computational.PrimeNoncePairControls
