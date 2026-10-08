import ExplainableCrypto.Helios.Symbolic.CiphertextGroupingExperiments

namespace ExplainableCrypto.Helios.Symbolic.CiphertextObservationExperiments
open ExplainableCrypto.Testing

private inductive Keys where
  | leaf (k : Nat)
  | mul (a b : Keys)
private def keys (depth seed : Nat) : Keys :=
  match depth with
  | 0 => .leaf (seed % 3)
  | d + 1 => if seed % 3 = 0 then .leaf (seed % 2)
      else .mul (keys d (seed / 3)) (keys d (seed / 3 + seed % 2))
private def first : Keys → Nat
  | .leaf k => k
  | .mul a _ => first a
private def leaves : Keys → List Nat
  | .leaf k => [k]
  | .mul a b => leaves a ++ leaves b
private def coherent (broken : Bool) : Keys → Bool
  | .leaf _ => true
  | .mul a b => coherent broken a && coherent broken b && (broken || first a == first b)

def coherenceCheck (seed : Nat) (broken := false) : Bool :=
  let t := Keys.mul (keys 3 seed) (keys 3 (seed + 1))
  coherent broken t == (leaves t).all (fun k => k == first t)

private structure Group where
  tag : Nat
  publicNonce : List Nat
  honestNonce : List Nat
  atoms : List Nat
  number : Option Nat
private def group (tag seed : Nat) : Group :=
  ⟨tag, if seed % 2 = 0 then [40] else [40, 40],
    if seed / 2 % 3 = 0 then [20] else if seed / 2 % 3 = 1 then [21] else [20, 20],
    [80 + seed / 6 % 2], if seed / 12 % 2 = 0 then none else some (seed / 24 % 2)⟩
private def nonce (g : Group) : List Nat :=
  if g.tag = 0 then g.publicNonce else if g.tag = 1 then g.honestNonce else g.publicNonce ++ g.honestNonce
private def honestSum (g : Group) (swap : Bool) : Nat :=
  (g.honestNonce.filter (fun i => if swap then i == 21 else i == 20)).length
private def message (g : Group) (swap : Bool) : List Nat × Option Nat :=
  if g.tag = 0 then (g.atoms, g.number)
  else if g.tag = 1 then ([], some (honestSum g swap))
  else (g.atoms, some (g.number.getD 0 + honestSum g swap))
private def observed (a b : Group) (swap : Bool) : Bool :=
  decide ((nonce a).Perm (nonce b)) && decide ((message a swap).1.Perm (message b swap).1) &&
    (message a swap).2 == (message b swap).2
private def predicted (a b : Group) : Bool :=
  if a.tag != b.tag then false
  else if a.tag = 0 then decide (a.publicNonce.Perm b.publicNonce) &&
    decide (a.atoms.Perm b.atoms) && a.number == b.number
  else if a.tag = 1 then decide (a.honestNonce.Perm b.honestNonce)
  else decide (a.honestNonce.Perm b.honestNonce) && decide (a.publicNonce.Perm b.publicNonce) &&
    decide (a.atoms.Perm b.atoms) && a.number.getD 0 == b.number.getD 0

def matrixCheck (seed : Nat) : Bool :=
  let a := group (seed % 3) (seed / 9)
  let b := group (seed / 3 % 3) (if seed / 27 % 2 = 0 then seed / 9 else seed / 9 + 12)
  (observed a b false == predicted a b) && (observed a b true == predicted a b)

#eval campaign "coherence ignores subtree key agreement (negative control)"
  (∀ n : Nat, coherenceCheck n true = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "recursive key coherence agrees with all leaf keys" (∀ n : Nat, coherenceCheck n = true) seed
    campaign "all grouped ciphertext cases preserve exact equality criteria" (∀ n : Nat, matrixCheck n = true) seed
  unless (List.range 256).all (fun i => coherenceCheck i && matrixCheck i) do
    throw (IO.userError "ciphertext-observation backstop failed")
  unless (List.range 9).all (fun i => (List.range 64).all (fun j => matrixCheck (9 * j + i))) do
    throw (IO.userError "ciphertext-observation directed matrix cases failed")
  IO.println "ciphertext-observation backstop: 256 inputs and 576 directed matrix inputs passed"

end ExplainableCrypto.Helios.Symbolic.CiphertextObservationExperiments
