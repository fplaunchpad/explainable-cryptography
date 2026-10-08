import ExplainableCrypto.Helios.Symbolic.PairObservationExperiments

namespace ExplainableCrypto.Helios.Symbolic.AtomicObservationExperiments
open ExplainableCrypto.Testing Historical

private def constant (seed : Nat) : Constant :=
  match seed % 4 with | 0 => .ok | 1 => .zero | 2 => .one | _ => .bottom
private def isAtom : Term V → Bool
  | .name _ | .const _ => true
  | _ => false
private def frame (seed : Nat) :=
  let n := seed % 5
  General.frame (HistoricalFrameExperiments.generatedNames n) (seed / 5 % 2 == 1)
    (BitCandidate.abstain n).substitution (BitCandidate.selected (0 : Fin (n + 1))).substitution

private def constantRecipe (seed : Nat) : Recipe 3 :=
  let n := seed % 5
  match constant (seed / 10) with
  | .ok => .ternary .checkspk (.var 0) ((Term.var 1).project 0) ((Term.var 1).project (n + 1))
  | .bottom => (Term.var 1).drop (fieldCount n)
  | c => .unary .fst (.binary .pair (.const c) (.const .bottom))

def outputCheck (seed : Nat) : Bool :=
  let φ := frame seed
  let name : Recipe 3 := .unary .fst (.binary .pair (.name (40 + seed % 7)) (.const .bottom))
  (normalizeRaw (φ.eval (constantRecipe seed)) == .const (constant (seed / 10))) &&
    (normalizeRaw (φ.eval name) == .name (40 + seed % 7))

def handleCheck (seed : Nat) : Bool :=
  let φ := frame seed
  !isAtom (normalizeRaw (φ.eval (.var ⟨seed / 10 % 3, Nat.mod_lt _ (by decide)⟩)))

def identityCheck (seed : Nat) : Bool :=
  let a : Ground := .const (constant seed)
  let b : Ground := .const (constant (seed / 4))
  let x : Ground := .name (40 + seed / 16 % 7)
  let y : Ground := .name (40 + seed / 112 % 7)
  ((normalizeRaw a == normalizeRaw b) == (constant seed == constant (seed / 4))) &&
    ((normalizeRaw x == normalizeRaw y) == (seed / 16 % 7 == seed / 112 % 7)) &&
    (normalizeRaw x != normalizeRaw a)

def omittedMinimum (seed : Nat) : Bool :=
  let r : Recipe 3 := (Term.var 1).drop (fieldCount (seed % 5))
  !isAtom (normalizeRaw ((frame seed).eval r)) || isAtom r

def constantCollapse (_seed : Nat) : Bool :=
  normalizeRaw (Term.const (V := Empty) .zero) == normalizeRaw (.const .one)

#eval campaign "atomic origins without minimum size (negative control)"
  (∀ n : Nat, omittedMinimum n = true) 1 true
#eval campaign "distinct constants collapse (negative control)"
  (∀ n : Nat, constantCollapse n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "initial handles are non-atomic and public atom outputs are exact"
      (∀ n : Nat, handleCheck n = true ∧ outputCheck n = true) seed
    campaign "literal atom equality retains type and identity" (∀ n : Nat, identityCheck n = true) seed
  unless (List.range 784).all (fun n => handleCheck n && outputCheck n && identityCheck n) do
    throw (IO.userError "atomic observation backstop failed")
  IO.println "atomic observation backstop: 784 inputs passed"

end ExplainableCrypto.Helios.Symbolic.AtomicObservationExperiments
