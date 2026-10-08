import ExplainableCrypto.Helios.Symbolic.ResultHandleSyntax
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulDecryptionExperiments

namespace ExplainableCrypto.Helios.Symbolic.ResultHandleExperiments
open ExplainableCrypto.Testing Historical General
private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10+i.val*(n+1)+j.val⟩
private def sample (n seed : Nat) : Recipe (ResultHandles n) :=
  let v : Recipe (ResultHandles n) := .var (resultSlot 0)
  let b : Recipe (ResultHandles n) := .var (resultOld 1)
  let c := Term.ternary .penc (.unary .pk v) (.binary .compose v (.name 40)) b
  match seed%7 with
  | 0 => .binary .add v (.const .zero)
  | 1 => .binary .pair b (.unary .pk v)
  | 2 => .binary .dec v c
  | 3 => .binary .dec (.binary .partialDecrypt v c) c
  | 4 => .spk v v v c
  | 5 => .unary .fst (.binary .pair v b)
  | _ => .ternary .checkspk v (.ternary .penc v v v) (.spk v v v (.ternary .penc v v v))

/-- Fixture-only normalization of purely numeric additions at every position.
It retains numeric zero next to nonnumeric atoms and does not decide full E. -/
private def numericCanon : Ground → Ground
  | .unary f a => .unary f (numericCanon a)
  | .binary f a b =>
    let t := Term.binary f (numericCanon a) (numericCanon b)
    if f = .add ∧ t.addSyntaxSummary.atoms = 0 then
      normalizeRaw (addNumeral (t.addSyntaxSummary.numeric.getD 0)) else t
  | .ternary f a b c => .ternary f (numericCanon a) (numericCanon b) (numericCanon c)
  | .spk a b c d => .spk (numericCanon a) (numericCanon b) (numericCanon c) (numericCanon d)
  | t => t
private def view (t : Ground) := normalizeRaw (numericCanon (normalizeRaw t))

def checkWith (normalize : Ground → Ground) (seed : Nat) : Bool :=
  let n := seed%5
  let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
  let right := (BitCandidate.abstain n).substitution
  let numbers : Fin (n+1) → Nat := fun j => if j.val=0 then 1 else 0
  let r := sample n seed
  [false,true].all fun swap =>
    let φ := expandedFrame (names n) swap left right []
    let ψ := frame (names n) swap left right
    let rs := [r,Term.binary .add r (.var (resultSlot ⟨seed%(n+1),Nat.mod_lt _ (by omega)⟩))]
    rs.all fun t => normalize (φ.eval (t.subst (fun i => .var (resultEmbedding i)))) ==
      normalize (ψ.eval (t.subst (resultNumeralRecipes numbers)))

def check := checkWith view

def everyResultZero (_ : Nat) : Bool :=
  let ns := names 0
  let left := (BitCandidate.selected (0 : Fin 1)).substitution
  let right := (BitCandidate.abstain 0).substitution
  let φ := expandedFrame ns false left right []
  decide ((normalizeRaw (φ.eval (.var (expandedResult 0)))).addSyntaxSummary = AddSummary.number 0)
def erasePartial (_ : Nat) : Bool :=
  let ns := names 0
  let c := (BitCandidate.abstain 0).substitution
  normalizeRaw ((expandedFrame ns false c c []).eval (.var (expandedPartial 0))) == .const .bottom

#eval campaign "result erasure maps every value to zero (negative control)" (∀ n : Nat, everyResultZero n = true) 1 true
#eval campaign "result erasure includes trustee partials (negative control)" (∀ n : Nat, erasePartial n = true) 1 true
#eval campaign "raw normalization alone tests full numeric equality (negative control)" (∀ n : Nat, checkWith normalizeRaw n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "shared numeral substitution through nested result-only recipes" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "result handle backstop failed")
  IO.println "result handle backstop: 2048 inputs, one through five candidates, both swaps, nested constructors/destructors and zero/one result slots"

end ExplainableCrypto.Helios.Symbolic.ResultHandleExperiments
