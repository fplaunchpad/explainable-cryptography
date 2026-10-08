import ExplainableCrypto.Helios.Computational.BitOracleCanary
import ExplainableCrypto.Helios.Computational.FairBitSampler
import ExplainableCrypto.Helios.Computational.UniformOperandCodec

/-! An executed loader for the actual chronological fair-bit word. The fixed
finite program consumes one width token per coin and reverses its accumulator
by stack moves. The fifth stack preserves the caller's modulus word. -/
namespace ExplainableCrypto.Helios.Computational.CoinWordLoader
open OracleComp OracleSpec BitOracleMachine

def encode : Option Bool → Fin 3
  | none => 0 | some false => 1 | some true => 2

/-- Ports: width, response, accumulator, output, retained modulus. -/
def code : Code 5 4 3 := ![
  .compute (.pop 0 (fun _ b => encode b) (.branch (fun v => v != 0)
    (.load (fun _ => 0) (.goto (fun _ => 1)))
    (.load (fun _ => 0) (.goto (fun _ => 3))))),
  .coin 1 2,
  .compute (.pop 1 (fun _ b => encode b)
    (.push 2 (fun v => v == 2) (.load (fun _ => 0) (.goto (fun _ => 0))))),
  .compute (.pop 2 (fun _ b => encode b) (.branch (fun v => v != 0)
    (.push 3 (fun v => v == 2) (.load (fun _ => 0) (.goto (fun _ => 3))))
    (.load (fun _ => 0) .halt)))]

def state (phase : Option (Fin 4)) (width response acc out modulus : List Bool) :
    Config 5 4 3 := ⟨phase, 0, ![width, response, acc, out, modulus]⟩

/-- Query-tree specification: the first response is the least-significant bit. -/
def word : Nat → OracleComp spec (List Bool)
  | 0 => pure []
  | n+1 => do
      let b ← liftM (spec.query .coin)
      let rest ← word n
      pure (b :: rest)

private theorem count_step (b : Bool) (width acc out modulus : List Bool) :
    step code (state (some 0) (b::width) [] acc out modulus) =
      pure (state (some 1) width [] acc out modulus, 4) := by
  cases b <;> simp [step, code, state, encode, localCost, Turing.TM2.stepAux]
  all_goals funext j; fin_cases j <;> rfl

private theorem count_done (acc out modulus : List Bool) :
    step code (state (some 0) [] [] acc out modulus) =
      pure (state (some 3) [] [] acc out modulus, 4) := by
  simp [step, code, state, encode, localCost, Turing.TM2.stepAux]

private theorem coin_step (width acc out modulus : List Bool) :
    step code (state (some 1) width [] acc out modulus) = (do
      let b ← liftM (spec.query .coin)
      pure (state (some 2) width [b] acc out modulus, 2)) := by
  simp [step, code, state, resume]
  congr 1
  funext b
  congr 2
  funext j; fin_cases j <;> rfl

private theorem collect_step (b : Bool) (width acc out modulus : List Bool) :
    step code (state (some 2) width [b] acc out modulus) =
      pure (state (some 0) width [] (b::acc) out modulus, 4) := by
  cases b <;> simp [step, code, state, encode, localCost, Turing.TM2.stepAux]
  all_goals funext j; fin_cases j <;> rfl

private theorem reverse_step (b : Bool) (acc out modulus : List Bool) :
    step code (state (some 3) [] [] (b::acc) out modulus) =
      pure (state (some 3) [] [] acc (b::out) modulus, 5) := by
  cases b <;> simp [step, code, state, encode, localCost, Turing.TM2.stepAux]
  all_goals funext j; fin_cases j <;> rfl

private theorem reverse_done (out modulus : List Bool) :
    step code (state (some 3) [] [] [] out modulus) =
      pure (state none [] [] [] out modulus, 5) := by
  simp [step, code, state, encode, localCost, Turing.TM2.stepAux]

private theorem reverse_run (acc out modulus : List Bool) :
    run code (acc.length+1) (state (some 3) [] [] acc out modulus) =
      pure (state none [] [] [] (acc.reverse ++ out) modulus, 5*acc.length+5) := by
  induction acc generalizing out with
  | nil => simp [run, reverse_done]
  | cons b acc ih =>
    rw [List.length_cons, Nat.add_right_comm, run, reverse_step]
    simp only [pure_bind]
    rw [ih]
    simp [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_comm]

private theorem loop (width acc out modulus : List Bool) :
    run code (4*width.length+acc.length+2) (state (some 0) width [] acc out modulus) =
      (fun bits => (state none [] [] [] (acc.reverse ++ bits ++ out) modulus,
        15*width.length+5*acc.length+9)) <$> word width.length := by
  induction width generalizing acc with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, word, map_pure]
    rw [show acc.length+2 = (acc.length+1)+1 by omega, run, count_done]
    simp only [pure_bind, reverse_run]
    simp only [List.append_nil]
    apply congrArg (pure : Config 5 4 3 × Nat → OracleComp spec _)
    apply Prod.ext
    · rfl
    · omega
  | cons token width ih =>
    rw [show 4*(token::width).length+acc.length+2 =
      ((4*width.length+(false::acc).length+2)+1)+1+1 by simp; omega,
      run, count_step]
    simp only [pure_bind]
    rw [run, coin_step]
    simp only [bind_assoc, pure_bind]
    rw [show (token::width).length = width.length+1 from rfl, word]
    simp only [map_bind]
    apply bind_congr
    intro b
    change Bool at b
    rw [run, collect_step]
    simp only [pure_bind]
    rw [show (false::acc).length = (b::acc).length from rfl, ih]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr
    intro bits
    apply congrArg (pure : Config 5 4 3 × Nat → OracleComp spec _)
    apply Prod.ext
    · simp [List.reverse_cons, List.append_assoc]
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- Complete oracle-tree equality, including every stack and the derived charge.
Width tokens and modulus are loaded words at this boundary. -/
theorem run_source (width modulus : List Bool) :
    run code (4*width.length+2) (state (some 0) width [] [] [] modulus) =
      (fun bits => (state none [] [] [] bits modulus, 15*width.length+9)) <$>
        word width.length := by
  simpa using loop width [] [] modulus

/-- Preserve each coin event in the existing raw-port interface. -/
def liftCoins : QueryImpl coinSpec (OracleComp spec) :=
  fun _ => liftM (spec.query .coin)

private theorem word_function (w : Nat) :
    word w = (fun f : Fin w → Fin 2 => List.ofFn (fun i => finTwoEquiv (f i))) <$>
      simulateQ liftCoins (Fin.mOfFn w (fun _ => finTwoEquiv.symm <$> coin)) := by
  induction w with
  | zero => simp [word, Fin.mOfFn]
  | succ w ih =>
    simp only [word, Fin.mOfFn, simulateQ_bind, simulateQ_pure,
      coin, simulateQ_spec_query, liftCoins, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def]
    apply bind_congr
    intro b
    change Bool at b
    rw [ih]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr
    intro f
    simp [List.ofFn_succ]

private theorem value_function {w : Nat} (f : Fin w → Fin 2) :
    bitsValue (List.ofFn (fun i => finTwoEquiv (f i))) =
      (finFunctionFinEquiv f).val := by
  rw [finFunctionFinEquiv_apply]
  induction w with
  | zero => simp [bitsValue]
  | succ w ih =>
    rw [List.ofFn_succ]
    change Nat.bit (finTwoEquiv (f 0))
      (bitsValue (List.ofFn (fun i => finTwoEquiv (f i.succ)))) = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ',
      Nat.mul_left_comm _ 2, ← Finset.mul_sum]
    have hbit : Nat.bit (finTwoEquiv (f 0)) 0 = (f 0).val := by
      generalize f 0 = a
      fin_cases a <;> rfl
    simp only [Nat.bit_val, Nat.mul_zero, Nat.zero_add] at hbit
    simp only [Nat.bit_val]
    omega

/-- Numeric observation agrees with the original sampler as a query tree.
`bitsValue` here observes the produced word; it is not a free machine instruction. -/
theorem word_index (w : Nat) :
    bitsValue <$> word w = simulateQ liftCoins (Fin.val <$> sampleFairBitIndex w) := by
  rw [word_function]
  simp only [sampleFairBitIndex, simulateQ_map, Functor.map_map]
  congr 1
  funext f
  exact value_function f

/-- Observe the executed output through the original modulo sampler's value.
Division is still an observation here; linking the executed division is separate. -/
theorem run_modulo (q : Nat) [NeZero q] (width modulus : List Bool) :
    (fun result => bitsValue (result.1.stk 3) % q) <$>
      run code (4*width.length+2) (state (some 0) width [] [] [] modulus) =
      simulateQ liftCoins (Fin.val <$> sampleFairBitModulo q width.length) := by
  rw [run_source]
  have h := congrArg (fun computation : OracleComp spec Nat =>
    (fun n => n % q) <$> computation) (word_index width.length)
  simpa [sampleFairBitModulo, simulateQ_map, Functor.map_map, state] using h

/-- Every response branch returns exactly the requested number of bits. -/
theorem word_length (w : Nat) (bits : List Bool) (h : bits ∈ support (word w)) :
    bits.length = w := by
  induction w generalizing bits with
  | zero => simpa [word] using h
  | succ w ih =>
    rw [word] at h
    obtain ⟨b,_,hb⟩ := mem_support_bind_peel _ _ h
    change Bool at b
    obtain ⟨rest,hr,he⟩ := mem_support_bind_peel _ _ hb
    have heq : bits = b::rest := by simpa using he
    subst bits
    simp [ih rest hr]

end ExplainableCrypto.Helios.Computational.CoinWordLoader
