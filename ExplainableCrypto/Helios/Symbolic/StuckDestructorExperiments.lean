import ExplainableCrypto.Helios.Symbolic.MinimumDestructorExperiments

namespace ExplainableCrypto.Helios.Symbolic.StuckDestructorExperiments
open ExplainableCrypto.Testing Historical
private def reveal (t : Term V) := Term.unary .fst (.binary .pair t (.const .bottom))
private def selector (seed : Nat) : Unary := if seed % 2 = 0 then .fst else .snd

def projectionCheck (seed : Nat) : Bool :=
  let f := selector seed
  let g := selector (seed / 2)
  let x := 40 + seed / 4 % 3
  let y := 40 + seed / 12 % 3
  let a : Ground := .unary f (reveal (.name x))
  let b : Ground := .unary g (reveal (.name y))
  (normalizeRaw a == .unary f (.name x)) &&
    ((normalizeRaw a == normalizeRaw b) == ((f == g) && (x == y)))

def decryptionCheck (seed : Nat) : Bool :=
  let a := 40 + seed % 3
  let b := 50 + seed / 3 % 3
  let c := 40 + seed / 9 % 3
  let d := 50 + seed / 27 % 3
  let x : Ground := .binary .dec (reveal (.name a)) (reveal (.name b))
  let y : Ground := .binary .dec (reveal (.name c)) (reveal (.name d))
  (normalizeRaw x == .binary .dec (.name a) (.name b)) &&
    ((normalizeRaw x == normalizeRaw y) == ((a == c) && (b == d)))

def wrongKeyCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let φ := General.frame (HistoricalFrameExperiments.generatedNames n) (seed / 5 % 2 == 1)
    (BitCandidate.abstain n).substitution (BitCandidate.selected (0 : Fin (n + 1))).substitution
  let r : Recipe 3 := .binary .dec (.name (40 + seed % 3)) ((Term.var 1).project (seed / 10 % (n + 1)))
  match normalizeRaw (φ.eval r) with | .binary .dec _ _ => true | _ => false

def projectionWithoutNoPair (_seed : Nat) : Bool :=
  let a : Ground := .binary .pair (.const .one) (.const .zero)
  let b : Ground := .binary .pair (.const .one) (.const .one)
  (normalizeRaw (.unary .fst a) != normalizeRaw (.unary .fst b)) || (normalizeRaw a == normalizeRaw b)

def decryptionWithoutNoMatch (_seed : Nat) : Bool :=
  let a : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 50) (.const .zero)
  let b : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 51) (.const .zero)
  (normalizeRaw (.binary .dec (.name 40) a) != normalizeRaw (.binary .dec (.name 40) b)) ||
    (normalizeRaw a == normalizeRaw b)

#eval campaign "projection injectivity without no-pair premise (negative control)"
  (∀ n : Nat, projectionWithoutNoPair n = true) 1 true
#eval campaign "decryption injectivity without no-match premise (negative control)"
  (∀ n : Nat, decryptionWithoutNoMatch n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "stuck projections retain selector and reduced argument" (∀ n : Nat, projectionCheck n = true) seed
    campaign "stuck decryptions retain both reduced arguments" (∀ n : Nat, decryptionCheck n = true) seed
    campaign "public wrong keys leave honest ciphertext decryptions stuck" (∀ n : Nat, wrongKeyCheck n = true) seed
  unless (List.range 256).all (fun n => projectionCheck n && decryptionCheck n && wrongKeyCheck n) do
    throw (IO.userError "stuck destructor backstop failed")
  IO.println "stuck destructor backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.StuckDestructorExperiments
