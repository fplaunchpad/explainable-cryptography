import ExplainableCrypto.Helios.Symbolic.CiphertextCombinationExperiments

namespace ExplainableCrypto.Helios.Symbolic.MixedCiphertextExperiments
open ExplainableCrypto.Testing Historical

private def factors : Ground → List Ground
  | .binary .compose a b => factors a ++ factors b
  | t => [t]
private def atoms : Ground → List Ground
  | .binary .add a b => atoms a ++ atoms b
  | .const .zero | .const .one => []
  | t => [t]
private def sameFactors (a b : Ground) : Bool := decide ((factors a).Perm (factors b))
private def sameSum (a b : Ground) : Bool :=
  decide ((atoms a).Perm (atoms b)) && a.addSummary.numeric == b.addSummary.numeric
private def candidate (n : Nat) (zero : Bool) (p : Fin (n + 1)) : BitCandidate n :=
  if zero then .abstain n else .selected p

/-- Exact comparisons for the generated named/opaque-factor and numeric families,
not a full-E equality decider for arbitrary recipe values. -/
def mixedCheck (seed : Nat) (padExpected : Bool := true) : Bool :=
  let n := seed % 5
  let mode := seed / 5 % 4
  let swap := seed / 20 % 2 == 1
  let pos : Fin (n + 1) := ⟨seed / 40 % (n + 1), Nat.mod_lt _ (by omega)⟩
  let pos' : Fin (n + 1) := ⟨(seed / 40 + 1) % (n + 1), Nat.mod_lt _ (by omega)⟩
  let ns := HistoricalFrameExperiments.generatedNames n
  let φ := General.frame ns swap (candidate n (mode % 2 == 0) pos).substitution
    (candidate n (mode / 2 == 0) pos').substitution
  let i : General.HonestIndex n := (0, pos)
  let j : General.HonestIndex n := (1, pos')
  let a := Combination.mul (.leaf i) (.mul (.leaf j) (.leaf i))
  let equalBag := seed / 40 % 2 == 0
  let b := if equalBag then Combination.mul (.leaf j) (.mul (.leaf i) (.leaf i))
    else Combination.mul (.leaf i) (.leaf j)
  let reveal := fun t : Recipe 3 => Term.unary .fst (.binary .pair t (.const .bottom))
  let r : Recipe 3 := match seed / 80 % 4 with
    | 0 => .name 40
    | 1 => .binary .compose (.name 40) (.name 41)
    | 2 => (Term.var 1).project 0
    | _ => .ternary .penc (.var 0) (.name 42) (.name 43)
  let s := if seed / 160 % 3 = 0 then reveal r
    else if seed / 160 % 3 = 1 then r else .binary .compose r (.name 44)
  let p : Recipe 3 := if seed / 320 % 2 = 0 then .name 80 else .const .zero
  let q := match seed / 40 % 4 with
    | 0 => .binary .add p (.const .zero)
    | 1 => .binary .add p (.const .one)
    | 2 => .name 81
    | _ => reveal p
  let product := fun r p t => Term.binary .mul (.ternary .penc (.var 0) r p) (General.combinationRecipe t)
  let actual := match normalizeRaw (φ.eval (product r p a)), normalizeRaw (φ.eval (product s q b)) with
    | .ternary .penc k nr m, .ternary .penc k' ns m' => k == k' && sameFactors nr ns && sameSum m m'
    | _, _ => false
  let pad := fun t => if padExpected then Term.binary .add t (.const .zero) else t
  let expected := decide (([i, j, i] : List (General.HonestIndex n)).Perm (if equalBag then [j, i, i] else [i, j])) &&
    sameFactors (normalizeRaw (φ.eval r)) (normalizeRaw (φ.eval s)) &&
    sameSum (normalizeRaw (φ.eval (pad p))) (normalizeRaw (φ.eval (pad q)))
  actual == expected

#eval campaign "mixed ciphertext equality without payload padding (negative control)"
  (∀ n : Nat, mixedCheck n false = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "mixed ciphertext equality reduces to protected nonce and padded payload observations"
      (∀ n : Nat, mixedCheck n = true) seed
  unless (List.range 256).all mixedCheck do
    throw (IO.userError "mixed-ciphertext backstop failed")
  IO.println "mixed-ciphertext backstop: 256 inputs passed"
  unless (List.range 320).all (fun n => mixedCheck (320 + n)) do
    throw (IO.userError "mixed-ciphertext zero-payload and changed-remainder cases failed")
  IO.println "mixed-ciphertext directed cases: inputs 320 through 639 passed"

end ExplainableCrypto.Helios.Symbolic.MixedCiphertextExperiments
