import ExplainableCrypto.Helios.Symbolic.DecryptionProbeExperiments

namespace ExplainableCrypto.Helios.Symbolic.ValueShapeExperiments
open ExplainableCrypto.Testing Historical
private def shape (t : Ground) : Nat := match normalizeRaw t with
  | .binary .pair _ _ => 1 | .ternary .penc _ _ _ => 2 | .binary .partialDecrypt _ _ => 3 | _ => 0
private def recipe : Nat → Nat → Recipe 3
  | 0, seed => match seed % 6 with
    | 0 => .var 0 | 1 => .var 1 | 2 => .var 2
    | 3 => .const .zero | 4 => .const .one | _ => .name (40 + seed % 5)
  | depth+1, seed =>
    let a := recipe depth (seed / 13 + 1)
    let b := recipe depth (seed / 17 + 3)
    let c := recipe depth (seed / 19 + 5)
    match seed % 13 with
    | 0 => .unary .fst a | 1 => .unary .snd a | 2 => .unary .pk a
    | 3 => .binary .pair a b | 4 => .binary .partialDecrypt a b
    | 5 => .binary .dec a b | 6 => .binary .mul a b
    | 7 => .binary .add a b | 8 => .binary .compose a b
    | 9 => .ternary .penc a b c | 10 => .ternary .checkspk a b c
    | 11 => .spk a b c a | _ => (Term.var 1).project (seed % 5)

def shapeCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let ns := HistoricalFrameExperiments.generatedNames n
  let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
  let right := (BitCandidate.abstain n).substitution
  let r := recipe (1 + seed / 5 % 3) (seed / 15)
  shape ((General.frame ns false left right).eval r) == shape ((General.frame ns true left right).eval r)

def secretPolicyOmitted (_seed : Nat) : Bool :=
  let ns := HistoricalFrameExperiments.generatedNames 0
  let left := (BitCandidate.selected (0 : Fin 1)).substitution
  let right := (BitCandidate.abstain 0).substitution
  let bit : Recipe 3 := .binary .dec (.name 0) ((Term.var 1).project 0)
  let r := Term.binary .mul (.ternary .penc bit (.name 40) (.name 50))
    (.ternary .penc (.const .one) (.name 41) (.name 51))
  shape ((General.frame ns false left right).eval r) == shape ((General.frame ns true left right).eval r)

def everyDestructorStuck (_seed : Nat) : Bool :=
  let r : Ground := .unary .fst (.binary .pair (.binary .partialDecrypt (.name 40) (.name 50)) (.const .bottom))
  shape r == 0

#eval campaign "value shape with secret-key policy omitted (negative control)" (∀ n : Nat, secretPolicyOmitted n = true) 1 true
#eval campaign "universal destructor stuckness (negative control)" (∀ n : Nat, everyDestructorStuck n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "public recipe constructor shapes survive candidate swap" (∀ n : Nat, shapeCheck n = true) seed
  unless (List.range 4096).all shapeCheck do
    throw (IO.userError "value-shape backstop failed")
  IO.println "value-shape backstop: 4096 inputs passed"

end ExplainableCrypto.Helios.Symbolic.ValueShapeExperiments
