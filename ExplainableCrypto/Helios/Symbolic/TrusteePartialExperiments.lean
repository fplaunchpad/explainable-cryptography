import ExplainableCrypto.Helios.Symbolic.PublishedFrameExperiments

namespace ExplainableCrypto.Helios.Symbolic.TrusteePartialExperiments
open ExplainableCrypto.Testing Historical General

def check (seed : Nat) : Bool :=
  [false,true].all (fun swap =>
    [0,1].all (fun j : Fin 2 =>
      let ns := LocalRootSPOT.names
      let c := tallyCiphertext ns swap LocalRootSPOT.left LocalRootSPOT.right [] j
      let other := tallyCiphertext ns swap LocalRootSPOT.left LocalRootSPOT.right [] (if j=0 then 1 else 0)
      let a := tallyPartial ns swap LocalRootSPOT.left LocalRootSPOT.right [] j
      let payload : Ground := .binary .pair (.name (40+seed%7)) (.const (if seed%2=0 then .zero else .one))
      let fresh := keyCiphertext a (.name (60+seed%5)) payload
      decide ((normalizeRaw (.binary .dec a c)).addSyntaxSummary = AddSummary.number j.val) &&
      (normalizeRaw (.binary .dec a other) == .binary .dec (normalizeRaw a) (normalizeRaw other)) &&
      (normalizeRaw (.binary .dec a fresh) == payload)))

def ignoreBinding (_ : Nat) : Bool :=
  let ns := LocalRootSPOT.names
  let a := tallyPartial ns false LocalRootSPOT.left LocalRootSPOT.right [] 0
  let c := tallyCiphertext ns false LocalRootSPOT.left LocalRootSPOT.right [] 1
  normalizeRaw (.binary .dec a c) == .const .one

def omitStructuredE5 (_ : Nat) : Bool :=
  let a := tallyPartial LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right [] 0
  let c := keyCiphertext a (.name 60) (.name 90)
  normalizeRaw (.binary .dec a c) == .binary .dec (normalizeRaw a) (normalizeRaw c)

#eval campaign "trustee partial may ignore whole ciphertext binding (negative control)"
  (∀ n : Nat, ignoreBinding n = true) 1 true
#eval campaign "trustee partial can never act as an E5 key (negative control)"
  (∀ n : Nat, omitStructuredE5 n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "trustee partial matches, wrong candidate and newly constructed E5"
      (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "trustee partial backstop failed")
  IO.println "trustee partial backstop: 2048 inputs, two candidates, both swaps, varied payloads and nonces"

end ExplainableCrypto.Helios.Symbolic.TrusteePartialExperiments
