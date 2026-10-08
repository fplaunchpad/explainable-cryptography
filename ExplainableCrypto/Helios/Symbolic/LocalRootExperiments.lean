import ExplainableCrypto.Helios.Symbolic.ObservationAssemblySPOT

namespace ExplainableCrypto.Helios.Symbolic.LocalRootExperiments
open ExplainableCrypto.Testing

/-- A permitted secret-key name would make the explicit pk root nonminimum. -/
def exposedKey (_ : Nat) : Bool :=
  let r : Recipe 1 := .unary .pk (.name 40)
  let φ : Frame ∅ 1 := ⟨fun _ => .unary .pk (.name 40)⟩
  !(normalizeRaw (φ.eval r) == normalizeRaw (φ.eval (.var 0))) || r.nodeCount ≤ 1

def publishedPartial (_ : Nat) : Bool :=
  let r : Recipe 1 := .binary .partialDecrypt (.name 40) (.name 41)
  let φ : Frame ∅ 1 := ⟨fun _ => .binary .partialDecrypt (.name 40) (.name 41)⟩
  !(normalizeRaw (φ.eval r) == normalizeRaw (φ.eval (.var 0))) || r.nodeCount ≤ 1

/-- Bounded raw-equality probes; minima themselves are established by Lean,
not by this deliberately incomplete competitor pool. -/
def check (seed : Nat) : Bool :=
  let a : Recipe 3 := .name (40 + seed % 4)
  let b : Recipe 3 := .name (50 + seed % 3)
  let atoms : List (Recipe 3) := [a,b,.var 0,.var 1,.var 2,.const .zero,.const .one]
  let competitors := atoms ++ atoms.flatMap (fun t => [.unary .fst t,.unary .snd t,.unary .pk t])
  let roots : List (Recipe 3) := [.unary .pk a, .binary .partialDecrypt a (.var 0),
    .spk (.var 0) a b (.var 1), .unary .fst a, .unary .snd a,
    .binary .dec (.var 0) a, .ternary .checkspk a b (.var 0)]
  [false,true].all fun swap =>
    let φ := ObservationAssemblySPOT.world swap
    roots.all fun r => competitors.all fun s =>
      !(s.nodeCount < r.nodeCount) ||
      !(normalizeRaw (φ.eval r) == normalizeRaw (φ.eval s))

#eval campaign "minimum pk root without secret-name restriction (negative control)"
  (∀ n : Nat, exposedKey n = true) 1 true
#eval campaign "minimum partial root in a publishing frame (negative control)"
  (∀ n : Nat, publishedPartial n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "local minimum roots versus bounded public competitors" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "local root backstop failed")
  IO.println "local root backstop: 2048 inputs, both swaps, seven roots and 28 competitors"

end ExplainableCrypto.Helios.Symbolic.LocalRootExperiments
