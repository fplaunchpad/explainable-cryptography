import ExplainableCrypto.Helios.Symbolic.ProjectionTransportSPOT

namespace ExplainableCrypto.Helios.Symbolic.CiphertextSelectorExperiments
open ExplainableCrypto.Testing
open Historical General

private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10 + i.val * (n+1) + j.val⟩

def collidingMinimum (_ : Nat) : Bool :=
  let φ := frame ProofObservationSPOT.colliding false LocalRootSPOT.right LocalRootSPOT.right
  let a : Recipe 3 := (Term.var 1).project 1
  let b : Recipe 3 := (Term.var 1).project 0
  !(normalizeRaw (φ.eval a) == normalizeRaw (φ.eval b)) || a.nodeCount ≤ b.nodeCount

def lostMultiplicity (_ : Nat) : Bool :=
  let t : Combination Nat := .mul (.leaf 0) (.leaf 0)
  decide (t.indices = (Combination.leaf 0).indices)

def check (seed : Nat) : Bool :=
  let n := seed % 5
  let i : Fin 2 := ⟨seed % 2, by omega⟩
  let j : Fin (n+1) := ⟨seed % (n+1), Nat.mod_lt _ (by omega)⟩
  let index : HonestIndex n := (i,j)
  let leaf (k : Nat) : CiphertextAssembly n :=
    if (seed+k) % 3 = 0 then .constructed (.var 0) (.name (40+k)) (.const .zero)
    else .honest index
  let tree := (List.range (seed % 6)).foldl (fun t k => .mul t (leaf (k+1))) (leaf 0)
  let singleton := decide (tree.group = .honest (.leaf index)) == decide (tree = .honest index)
  let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
  let right := (BitCandidate.abstain n).substitution
  singleton && [false,true].all (fun swap =>
    let φ := frame (names n) swap left right
    let r : Recipe 3 := (Term.var i.succ).project j.val
    (normalizeRaw (φ.eval r) == normalizeRaw (ciphertext (names n) i (choice swap left right i).value j)) &&
    (r.nodeCount == j.val+2) &&
    ((List.range (fieldCount n + 1)).all fun k =>
      ((Term.var i.succ : Recipe 3).drop k).nodeCount == k+1))

#eval campaign "honest ciphertext minima without fresh nonces (negative control)"
  (∀ n : Nat, collidingMinimum n = true) 1 true
#eval campaign "ciphertext occurrence bags treated as sets (negative control)"
  (∀ n : Nat, lostMultiplicity n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "honest singleton assemblies and indexed ciphertext/tail fixtures" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "ciphertext selector backstop failed")
  IO.println "ciphertext selector backstop: 2048 inputs, one through five candidates, both swaps"

end ExplainableCrypto.Helios.Symbolic.CiphertextSelectorExperiments
