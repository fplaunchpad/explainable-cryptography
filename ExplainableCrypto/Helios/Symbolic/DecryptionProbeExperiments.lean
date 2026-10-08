import ExplainableCrypto.Helios.Symbolic.StuckDestructorExperiments

namespace ExplainableCrypto.Helios.Symbolic.DecryptionProbeExperiments
open ExplainableCrypto.Testing
private def reveal (t : Term V) := Term.unary .fst (.binary .pair t (.const .bottom))
private def fixture (seed : Nat) : Ground × Ground × Ground × Ground :=
  let k : Ground := reveal (.name 40)
  let binding : Ground := reveal (.ternary .penc (.unary .pk (.name 40)) (.name (50 + seed / 3 % 2)) (.name 90))
  let a := Term.binary .partialDecrypt k binding
  let key := if seed % 3 = 0 then .unary .pk a else if seed % 3 = 1 then .unary .pk k else .unary .pk (.name 41)
  let b := reveal (.ternary .penc key (.name 50) (reveal (.name 90)))
  (a, b, key, k)

def probeCheck (seed : Nat) : Bool :=
  let (a,b,key,k) := fixture seed
  let direct := normalizeRaw key == normalizeRaw (.unary .pk a)
  let binding := match a with | .binary .partialDecrypt _ v => normalizeRaw v == normalizeRaw b | _ => false
  let boundMatch := (normalizeRaw key == normalizeRaw (.unary .pk k)) && binding
  (normalizeRaw (.binary .dec a b) == .name 90) == (direct || boundMatch)

def omitDirect (_seed : Nat) : Bool :=
  let (a,b,key,k) := fixture 0
  let binding := match a with | .binary .partialDecrypt _ v => normalizeRaw v == normalizeRaw b | _ => false
  (normalizeRaw (.binary .dec a b) == .name 90) == ((normalizeRaw key == normalizeRaw (.unary .pk k)) && binding)

def omitBinding (_seed : Nat) : Bool :=
  let (a,b,key,k) := fixture 4
  (normalizeRaw (.binary .dec a b) == .name 90) ==
    ((normalizeRaw key == normalizeRaw (.unary .pk a)) || (normalizeRaw key == normalizeRaw (.unary .pk k)))

def sizeCheck (seed : Nat) : Bool :=
  let u : Recipe 3 := (Term.var 0).drop (seed % 5)
  let v : Recipe 3 := (Term.var 1).drop (seed / 5 % 5)
  let k : Recipe 3 := (Term.var 2).drop (seed / 25 % 5)
  let b := Term.ternary .penc k (.name 50) (.name 90)
  let a := Term.binary .partialDecrypt u v
  let bound := (Term.binary .dec a b).nodeCount
  decide ((Term.unary .pk a).nodeCount + k.nodeCount < bound ∧
    (Term.unary .pk u).nodeCount + k.nodeCount < bound ∧ v.nodeCount + b.nodeCount < bound)

#eval campaign "partial-key probe omitting E5 (negative control)" (∀ n : Nat, omitDirect n = true) 1 true
#eval campaign "partial-key probe omitting ciphertext binding (negative control)" (∀ n : Nat, omitBinding n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "partial-key matches equal direct-or-bound probes" (∀ n : Nat, probeCheck n = true) seed
    campaign "all partial-key public probes are strictly smaller" (∀ n : Nat, sizeCheck n = true) seed
  unless (List.range 512).all (fun n => probeCheck n && sizeCheck n) do
    throw (IO.userError "partial-key probe backstop failed")
  IO.println "partial-key probe backstop: 512 inputs passed"

end ExplainableCrypto.Helios.Symbolic.DecryptionProbeExperiments
