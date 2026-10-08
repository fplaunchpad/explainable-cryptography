import ExplainableCrypto.Helios.Symbolic.MinimumTransportExperiments

namespace ExplainableCrypto.Helios.Symbolic.ObservationAssemblyExperiments
open ExplainableCrypto.Testing

/-- All ground syntax cases used by the common-normal-value assembly. -/
def branch : Ground → Nat
  | .name _ => 0
  | .var v => nomatch v
  | .const _ => 1
  | .unary .pk _ => 2
  | .unary .fst _ => 3
  | .unary .snd _ => 4
  | .binary .pair _ _ => 5
  | .binary .partialDecrypt _ _ => 6
  | .binary .dec _ _ => 7
  | .binary .mul _ _ => 8
  | .binary .add _ _ => 9
  | .binary .compose _ _ => 10
  | .ternary .penc _ _ _ => 11
  | .ternary .checkspk _ _ _ => 12
  | .spk _ _ _ _ => 13

private def fixtures (seed : Nat) : List (Ground × Nat) :=
  let a : Ground := .name (40 + seed % 3)
  let b : Ground := .name (50 + seed % 5)
  let c : Ground := .name 60
  let enc : Ground := .ternary .penc (.unary .pk a) b (.const .zero)
  [(a,0), (.const .zero,1), (.const .one,1), (.const .ok,1), (.const .bottom,1),
   (.unary .pk a,2), (.unary .fst a,3), (.unary .snd a,4),
   (.binary .pair a b,5), (.binary .partialDecrypt a b,6),
   (.binary .dec a b,7), (.binary .mul a b,8), (.binary .add a b,9),
   (.binary .compose a b,10), (enc,11), (.ternary .checkspk a b c,12),
   (.spk a b c enc,13),
   (.unary .fst (.binary .pair a b),0), (.binary .dec a enc,1),
   (.binary .dec (.binary .partialDecrypt a enc) enc,1),
   (.binary .mul enc enc,11),
   (.ternary .checkspk (.unary .pk a) enc (.spk (.unary .pk a) b (.const .zero) enc),1)]

def rawHeadPreserved (_ : Nat) : Bool :=
  let t : Ground := .unary .fst (.binary .pair (.name 40) (.name 41))
  decide (branch t = branch (normalizeRaw t))

def check (seed : Nat) : Bool :=
  (fixtures seed).all fun p => branch (normalizeRaw p.1) == p.2

#eval campaign "raw head used as normal observation branch (negative control)"
  (∀ n : Nat, rawHeadPreserved n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "normal observation branch fixtures" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "observation assembly backstop failed")
  IO.println "observation assembly backstop: 2048 inputs, 22 fixtures each, all 14 branch classes"

end ExplainableCrypto.Helios.Symbolic.ObservationAssemblyExperiments
