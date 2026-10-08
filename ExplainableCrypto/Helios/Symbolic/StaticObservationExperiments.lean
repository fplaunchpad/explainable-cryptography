import ExplainableCrypto.Helios.Symbolic.GeneralCandidateExperiments

namespace ExplainableCrypto.Helios.Symbolic.StaticObservationExperiments
open ExplainableCrypto.Testing Historical HistoricalFrameExperiments

private def candidate (n mode pos : Nat) : BitCandidate n :=
  if mode % 2 = 0 then .abstain n else .selected ⟨pos % (n + 1), Nat.mod_lt _ (by omega)⟩

/-- A bounded raw-normalization proxy. It is not a full-E equality decision. -/
def sameObservations (left right : Fin 3 → Ground) (rs : List (Recipe 3)) : Bool :=
  let values := rs.map fun r => (normalizeRaw (r.subst left), normalizeRaw (r.subst right))
  values.all fun (a, b) => values.all fun (c, d) => (a == c) == (b == d)

def catalogue (n seed : Nat) : List (Recipe 3) :=
  let a := (Term.var 1 : Recipe 3).project (seed % (n + 1))
  let b := (Term.var 2 : Recipe 3).project (seed / 5 % (n + 1))
  let p := (Term.var 1 : Recipe 3).project (n + 1 + seed % (n + 1))
  let q := (Term.var 2 : Recipe 3).project (n + 1 + seed / 5 % (n + 1))
  let c : Recipe 3 := .ternary .penc (.var 0) (.name 80) (.const .one)
  let own : Recipe 3 := .ternary .penc (.unary .pk (.name 81)) (.name 82) (.const .zero)
  [.var 0, .var 1, .var 2, .const .zero, .const .one, .const .ok, .const .bottom,
   a, b, p, q, c, own,
   .binary .mul a b, .binary .mul b a, .binary .mul a a, .binary .mul c a,
   .ternary .checkspk (.var 0) a p, .ternary .checkspk (.var 0) b q,
   .ternary .checkspk (.var 0) b p,
   .ternary .checkspk (.var 0) (aggregateCiphertext n (.var 1))
     ((Term.var 1).project (2 * (n + 1))),
   .binary .dec (.name 81) own, .binary .dec (.name 81) a,
   .binary .dec (.binary .partialDecrypt (.name 81) own) own,
   .binary .dec (.binary .partialDecrypt (.name 81) a) a,
   .unary .fst (.binary .pair a b), .unary .snd (.binary .pair a b),
   (Term.var 1).drop (fieldCount n), (Term.var 1).project (fieldCount n)]

def observationCheck (seed : Nat) : Bool :=
  let n := seed % 5
  let mode := seed / 5 % 4
  let left := candidate n mode (seed / 20)
  let right := candidate n (mode / 2) (seed / 40)
  sameObservations (General.frame (generatedNames n) false left.substitution right.substitution).value
    (General.frame (generatedNames n) true left.substitution right.substitution).value (catalogue n seed)

/-- Dropping nonce injectivity lets a public equality test reveal a vote. -/
def collisionCheck (_seed : Nat) : Bool :=
  let ns : Names 1 := ⟨10, 11, fun _ _ => 20⟩
  let a := (BitCandidate.abstain 1).substitution
  let b := (BitCandidate.selected (0 : Fin 2)).substitution
  sameObservations (General.frame ns false a b).value (General.frame ns true a b).value
    [(Term.var 1).project 0, (Term.var 1).project 1]

/-- The nonce-only recipe policy would allow this secret-key recipe. -/
def exposedKeyCheck (_seed : Nat) : Bool :=
  let ns := generatedNames 0
  let a := (BitCandidate.abstain 0).substitution
  let b := (BitCandidate.selected (0 : Fin 1)).substitution
  sameObservations (General.frame ns false a b).value (General.frame ns true a b).value
    [.binary .dec (.name ns.secretKey) ((Term.var 1).project 0), .const .zero]

#eval campaign "static observations without nonce freshness (negative control)"
  (∀ n : Nat, collisionCheck n = true) 1 true
#eval campaign "static observations with exposed secret key (negative control)"
  (∀ n : Nat, exposedKeyCheck n = true) 1 true
#eval do
  for seed in [1, 7, 42] do
    campaign "finite raw observations of fresh general candidate frames"
      (∀ n : Nat, observationCheck n = true) seed
  unless (List.range 256).all observationCheck do
    throw (IO.userError "static-observation backstop failed")
  IO.println "static-observation backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.StaticObservationExperiments
