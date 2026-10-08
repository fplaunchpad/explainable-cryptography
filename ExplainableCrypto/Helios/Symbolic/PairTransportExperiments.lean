import ExplainableCrypto.Helios.Symbolic.CompleteProjectionSPOT

namespace ExplainableCrypto.Helios.Symbolic.PairTransportExperiments
open ExplainableCrypto.Testing
open Historical General

private def names (n : Nat) : Names n := ⟨0,1,fun i j => 10 + i.val * (n+1) + j.val⟩

def canonicalField (n k : Nat) (v : Fin 3) : Recipe 3 :=
  (Term.var v).project (if n = 0 ∧ k = 2 then 1 else k)

def canonicalRemainder (n k : Nat) (v : Fin 3) : Recipe 3 :=
  if k+1 = fieldCount n then .const .bottom else (Term.var v).drop (k+1)

def minimumChildrenForcePairMinimum (_ : Nat) : Bool :=
  let r : Recipe 3 := .binary .pair ((Term.var 1).project 0) ((Term.var 1).drop 1)
  r.nodeCount ≤ (Term.var (V := Fin 3) 1).nodeCount

def unconditionalEta (_ : Nat) : Bool :=
  let t : Ground := .name 40
  normalizeRaw (.binary .pair (.unary .fst t) (.unary .snd t)) == normalizeRaw t

def check (seed : Nat) : Bool :=
  let n := seed % 5
  let i : Fin 2 := ⟨seed % 2,by omega⟩
  let left := (BitCandidate.selected (0 : Fin (n+1))).substitution
  let right := (BitCandidate.abstain n).substitution
  [false,true].all fun swap =>
    let φ := frame (names n) swap left right
    (List.range (fieldCount n)).all fun k =>
      let a := canonicalField n k i.succ
      let b := canonicalRemainder n k i.succ
      let r : Recipe 3 := .binary .pair a b
      let t : Recipe 3 := (Term.var i.succ).drop k
      (normalizeRaw (φ.eval r) == normalizeRaw (φ.eval t)) &&
      decide (t.nodeCount < r.nodeCount) && decide (k+1 ≤ a.nodeCount) &&
      !(normalizeRaw (φ.eval (.binary .pair b a)) == normalizeRaw (φ.eval t))

#eval campaign "minimum children force minimum pair (negative control)"
  (∀ n : Nat, minimumChildrenForcePairMinimum n = true) 1 true
#eval campaign "pair eta on arbitrary values (negative control)"
  (∀ n : Nat, unconditionalEta n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "canonical field/remainder pairs reconstruct all honest tails" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "pair transport backstop failed")
  IO.println "pair transport backstop: 2048 inputs, one through five candidates, every nonempty tail, both swaps"

end ExplainableCrypto.Helios.Symbolic.PairTransportExperiments
