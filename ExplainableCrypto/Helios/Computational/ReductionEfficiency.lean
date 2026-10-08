import ExplainableCrypto.Helios.Computational.ElectionSecrecyFairBits
import ExplainableCrypto.Helios.Computational.NativeOracleTape

/-!
# An explicit external efficiency boundary for the exact reductions

The machine is one finite three-tape Boolean program for the whole parameter family, with only
head-local deterministic instructions and fair coins. Before a coin instruction its answer tape
must be blank: the existing native replacement then writes one bit, not an uncharged bulk reset.
There are no hash, storage, arithmetic, or callback oracles. Those operations, including all replay
iterations and the bounded fair-bit sampler, must be performed by the selected finite code.
In particular, the actual budget sum `D.p n + D.c n` used to select replay multiplicity is part
of the exact source family: domination by a polynomial does not implement that function.

This file defines a concrete machine claim, not `IsOraclePPTBy` and not a negligible-advantage
abbreviation. Equivalence of this three-tape step convention with a conventional probabilistic
Turing-machine definition is an external modeling argument; no pinned backend adequacy theorem
is asserted. Input representations and worst-case parameter bounds are explicit below.
-/
namespace ExplainableCrypto.Helios.Computational.ReductionEfficiency
open OracleComp OracleSpec NativeOracleTape

/-- Challenge words are representations, not host computations charged as machine steps.
The same public representation must be used by the computational DDH assumption. -/
structure GroupRepresentation (G : Nat → Type) where
  encode : ∀ n, G n → List Bool
  injective : ∀ n, Function.Injective (encode n)
  width : Polynomial Nat
  width_bound : ∀ n value, (encode n value).length ≤ width.eval n

abbrev Challenge (G : Nat → Type) (n : Nat) := G n × G n × G n × G n

/-- Unary length delimiter followed by the exact payload. -/
def field (word : List Bool) : List Bool :=
  List.replicate word.length true ++ false :: word

/-- Unary security parameter, followed by four separately framed group encodings.
No uncharged initialization of a callback, cache, or replay state is supplied. -/
def inputWord {G : Nat → Type} (representation : GroupRepresentation G)
    (n : Nat) (challenge : Challenge G n) : List Bool :=
  List.replicate n true ++ [false] ++
    field (representation.encode n challenge.1) ++
    field (representation.encode n challenge.2.1) ++
    field (representation.encode n challenge.2.2.1) ++
    field (representation.encode n challenge.2.2.2)

theorem inputWord_length {G : Nat → Type} (representation : GroupRepresentation G)
    (n : Nat) (challenge : Challenge G n) :
    (inputWord representation n challenge).length ≤ n + 8 * representation.width.eval n + 5 := by
  have h0 := representation.width_bound n challenge.1
  have h1 := representation.width_bound n challenge.2.1
  have h2 := representation.width_bound n challenge.2.2.1
  have h3 := representation.width_bound n challenge.2.2.2
  simp only [inputWord, field, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

/-- The hash branch is inaccessible for a realization's syntactically coin-only code. -/
def fairCoins : QueryImpl BitOracleMachine.spec ProbComp
  | .coin => uniformSample Bool
  | .hash _ => pure []

def coinOnly {labels : Nat} (code : Code labels) : Prop :=
  ∀ label current, match code label current with
    | .oracle .hash _ => False
    | _ => True

/-- A total readout whose default case is excluded by the required terminal invariant. -/
def outputBit {labels : Nat} (configuration : Config labels) : Bool :=
  configuration.work.head.getD false

/-- Code, semantic correspondence, and actual worst-case execution are one linked witness.
All inputs at a parameter and all fair-coin paths must halt; distributional agreement alone
cannot certify efficiency. The polynomial and finite code are fixed independently of `n`.
-/
structure Realization {G : Nat → Type} (representation : GroupRepresentation G)
    (family : ∀ n, Challenge G n → ProbComp Bool) where
  labels : Nat
  entry : Fin labels
  code : Code labels
  coins_only : coinOnly code
  time : Polynomial Nat
  terminal : ∀ n challenge configuration,
    configuration ∈ support (run code (time.eval n)
      (initial entry (inputWord representation n challenge))) →
    configuration.label = none ∧ configuration.work.head.isSome = true
  coin_ready : ∀ n challenge fuel configuration,
    configuration ∈ support (run code fuel
      (initial entry (inputWord representation n challenge))) →
    ∀ label next, configuration.label = some label →
      code label (heads configuration) = .oracle .coin next →
      configuration.answer = OracleTapeOutput.wordTape []
  correct : ∀ n challenge,
    evalDist (outputBit <$> simulateQ fairCoins (run code (time.eval n)
      (initial entry (inputWord representation n challenge)))) =
      evalDist (family n challenge)

def Efficient {G : Nat → Type} (representation : GroupRepresentation G)
    (family : ∀ n, Challenge G n → ProbComp Bool) : Prop :=
  Nonempty (Realization representation family)

namespace Controls
open Turing
open OracleTapeOutput (wordTape)

private def falseCode : Code 2 := fun label _ =>
  if label = 0 then .local 1 ![some (.write (some false)), none, none] else .halt

private def falseResult (word : List Bool) : Config 2 :=
  ⟨none, (wordTape word).write (some false), wordTape [], wordTape []⟩

theorem false_run (word : List Bool) :
    run falseCode 2 (initial 0 word) = pure (falseResult word) := by rfl

/-- The execution predicate is inhabited by an ordinary constant-output finite machine,
independently of the cryptographic assumptions or the selected group representation. -/
theorem constant_false_efficient {G : Nat → Type} (representation : GroupRepresentation G) :
    Efficient representation (fun _ _ => pure false) := by
  refine ⟨{
    labels := 2
    entry := 0
    code := falseCode
    coins_only := ?_
    time := 2
    terminal := ?_
    coin_ready := ?_
    correct := ?_ }⟩
  · intro label current
    fin_cases label <;> simp [falseCode]
  · intro n challenge configuration hc
    simp only [Polynomial.eval_ofNat] at hc
    rw [false_run] at hc
    have he : configuration = falseResult (inputWord representation n challenge) := by
      simpa using hc
    subst configuration
    exact ⟨rfl, rfl⟩
  · intro n challenge fuel configuration _ label next _ he
    fin_cases label <;> simp [falseCode] at he
  · intro n challenge
    simp only [Polynomial.eval_ofNat]
    rw [false_run]
    simp [outputBit, falseResult, Tape.write]

private def blankCode : Code 2 := fun label _ =>
  if label = 0 then .local 1 ![some (.write none), none, none] else .halt

/-- A halted blank head still decodes to the default false bit, but fails the required
successful-output invariant. Semantic readout alone does not make this a valid witness. -/
theorem blank_output_excluded (word : List Bool) :
    let result : Config 2 :=
      ⟨none, (wordTape word).write none, wordTape [], wordTape []⟩
    run blankCode 2 (initial 0 word) = pure result ∧
      result.label = none ∧ outputBit result = false ∧ result.work.head.isSome ≠ true := by
  exact ⟨rfl, rfl, rfl, by change false ≠ true; decide⟩

/-- The correspondence field distinguishes the executed false-output machine from true. -/
theorem wrong_output_excluded (word : List Bool) :
    evalDist (outputBit <$> simulateQ fairCoins (run falseCode 2 (initial 0 word))) ≠
      evalDist (pure true : ProbComp Bool) := by
  rw [false_run]
  simp only [simulateQ_pure, map_pure, outputBit, falseResult, Tape.write, evalDist_pure]
  intro h
  have hh := congrArg (fun measure : MeasureTheory.Measure Bool => measure {false}) h
  simp at hh

/-- Bounded observation with no executed instruction cannot satisfy successful halting. -/
theorem zero_fuel_live {labels : Nat} (code : Code labels) (entry : Fin labels)
    (word : List Bool) :
    (initial entry word) ∈ support (run code 0 (initial entry word)) ∧
      (initial entry word).label ≠ none := by simp [run, initial]

/-- An actual hash instruction cannot be hidden behind the harmless hash arm of fairCoins. -/
theorem hash_excluded : ¬ coinOnly (fun (_ : Fin 1) _ => .oracle .hash 0) := by
  intro h
  exact h 0 (fun _ => none)

/-- A nonblank old answer fails the coin-call convention; its wholesale deletion is not free. -/
theorem nonblank_answer_excluded : wordTape [false] ≠ wordTape [] := by
  intro h
  have hh := congrArg Tape.head h
  have : (some false : Option Bool) = none := hh
  cases this

#print axioms constant_false_efficient
#print axioms blank_output_excluded
#print axioms wrong_output_excluded
#print axioms zero_fuel_live
#print axioms hash_excluded
#print axioms nonblank_answer_excluded
end Controls

variable {q : Nat → Nat} [∀ n, Fact (q n).Prime] {G : Nat → Type}
  [∀ n, AddCommGroup (G n)] [∀ n, Module (ZMod (q n)) (G n)]
  [∀ n, DecidableEq (G n)]

/-- Every fixed accuracy degree has one uniform program and one polynomial runtime bound.
No uniform polynomial in the varying degree `k` is asserted or needed. -/
def MainReductionEfficient
    (D : ElectionSecrecyPrototype.PreparedFamily (fun n => ZMod (q n)) G)
    (representation : GroupRepresentation G) : Prop :=
  ∀ k, Efficient representation (fun n challenge => ElectionSecrecyFairBits.main D k n
    challenge.1 challenge.2.1 challenge.2.2.1 challenge.2.2.2)

def RejectionReductionEfficient
    (D : ElectionSecrecyPrototype.PreparedFamily (fun n => ZMod (q n)) G)
    (representation : GroupRepresentation G) : Prop :=
  Efficient representation (fun n challenge => ElectionSecrecyFairBits.reject D n
    challenge.1 challenge.2.1 challenge.2.2.1 challenge.2.2.2)

/-- DDH against this explicit uniform fair-coin machine class and the same group encoding.
Identifying it with an independently stated standard-PPT DDH assumption requires the external
machine-model/representation argument; it is not obtained from the backend-relative facade. -/
def DDHAssumption (representation : GroupRepresentation G) (generator : ∀ n, G n) : Prop :=
  ∀ family : ∀ n, Challenge G n → ProbComp Bool, Efficient representation family →
    negligible (fun n => ENNReal.ofReal (DiffieHellman.ddhDistAdvantage (F := ZMod (q n)) (generator n)
      (fun g a b t => family n (g, a, b, t))))

#print axioms inputWord_length
end ExplainableCrypto.Helios.Computational.ReductionEfficiency
