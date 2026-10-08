import ExplainableCrypto.Helios.Symbolic.TrusteeFreeSyntax
import ExplainableCrypto.Helios.Symbolic.ResultHandleExperiments

namespace ExplainableCrypto.Helios.Symbolic.TrusteeFreeExperiments
open ExplainableCrypto.Testing RewriteExperiments Historical General

/-- Fixture detector for literal and raw-reducible keys. It does not decide E. -/
def marker {V : Type} [DecidableEq V] : Term V → Bool
  | .name _ | .var _ | .const _ => true
  | .unary _ a => marker a
  | .binary f a b => marker a && marker b && !(f == .partialDecrypt && normalizeRaw a == .name 0)
  | .ternary _ a b c => marker a && marker b && marker c
  | .spk a b c d => marker a && marker b && marker c && marker d
private def bad : Term Nat := .binary .partialDecrypt (.name 0) (.name 40)
private def contexts (a : Term Nat) : List (Term Nat) :=
  [a,.unary .pk a,.spk a (.name 40) a (.const .zero),
   .binary .partialDecrypt a (.name 40),.ternary .penc (.name 40) a (.const .zero)]
def check (seed : Nat) : Bool :=
  let a := if seed%2=0 then .name 40 else bad
  let b := generatedTerm (seed%4) (seed+41)
  let c := if seed%3=0 then .name 0 else .unary .pk bad
  (backgroundPairs a b c).all (fun (l,r) =>
    (contexts l).zip (contexts r) |>.all (fun (x,y) => marker x == marker y)) &&
  (reductionPairs c a b (.binary .pair a b) a).all (fun (l,r) =>
    (contexts l).zip (contexts r) |>.all (fun (x,y) => !marker x || marker y))

-- The actual initial-frame check is written separately to keep the fixture
-- detector independent of any theorem about public-recipe interpretation.
def initialCheck (seed : Nat) : Bool :=
  let ns : Names 0 := ⟨0,1,fun i j => 10+i.val+j.val⟩
  [false,true].all fun swap =>
    let φ := frame ns swap (BitCandidate.abstain 0).substitution (BitCandidate.selected (0 : Fin 1)).substitution
    let r : Recipe 3 := .spk (.unary .pk (.var 0)) (.binary .partialDecrypt (.var 0) (.var 1))
      (.name (40+seed%5)) (.ternary .penc (.var 0) (.var 1) (.var 2))
    marker (φ.eval r)

-- Independently assembled E7 pairs: no destructor may discard a component.
def fusionCheck (seed : Nat) : Bool :=
  let k := generatedTerm (seed%4) (seed+3)
  let r := if seed%2=0 then bad else generatedTerm (seed%3) (seed+5)
  let s := generatedTerm (seed%4) (seed+7)
  let m := generatedTerm (seed%4) (seed+11)
  let n := if seed%3=0 then bad else generatedTerm (seed%3) (seed+13)
  marker (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n)) ==
    marker (.ternary .penc k (.binary .compose r s) (.binary .add m n))

def opaqueBlind (_ : Nat) := marker (.unary .pk bad)
def rawKeyBlind (_ : Nat) := marker (.binary .partialDecrypt (.unary .fst (.binary .pair (.name 0) (.const .zero))) (.name (V := Nat) 40))
def backward (_ : Nat) := marker (.unary .fst (.binary .pair (.const .zero) bad)) == marker (Term.const (V := Nat) .zero)

#eval campaign "trustee marker ignores opaque positions (negative control)" (∀ n : Nat, opaqueBlind n = true) 1 true
#eval campaign "trustee marker checks only raw literal keys (negative control)" (∀ n : Nat, rawKeyBlind n = true) 1 true
#eval campaign "trustee-free raw syntax reflects through erasure (negative control)" (∀ n : Nat, backward n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "trustee marker survives background equations and forward rules, with exact E7 reflection" (∀ n : Nat, check n && initialCheck n && fusionCheck n = true) seed
  unless (List.range 2048).all (fun n => check n && initialCheck n && fusionCheck n) do
    throw (IO.userError "trustee-free backstop failed")
  IO.println "trustee-free backstop: 2048 inputs, all seven oriented rules and eight background equations, opaque/partial-key contexts, actual initial frames in both swaps, bidirectional E7 component retention"

end ExplainableCrypto.Helios.Symbolic.TrusteeFreeExperiments
