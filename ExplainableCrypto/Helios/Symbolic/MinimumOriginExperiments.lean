import ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT
import ExplainableCrypto.Helios.Symbolic.RawNormalization
import ExplainableCrypto.Testing.Plausible

namespace ExplainableCrypto.Helios.Symbolic.MinimumOriginExperiments
open ExplainableCrypto.Testing Historical

def chain : Recipe 3 → Bool
  | .var _ => true
  | .unary .fst r | .unary .snd r => chain r
  | _ => false
def pairOrigin (r : Recipe 3) : Bool :=
  match r with | .binary .pair _ _ => true | _ => chain r
def proofOrigin (r : Recipe 3) : Bool :=
  match r with | .spk _ _ _ _ => true | _ => chain r

def subterms (r : Recipe 3) : List (Recipe 3) := r :: (match r with
  | .unary _ a => subterms a
  | .binary _ a b => subterms a ++ subterms b
  | .ternary _ a b c => subterms a ++ subterms b ++ subterms c
  | .spk a b c d => subterms a ++ subterms b ++ subterms c ++ subterms d
  | _ => [])

def certificate (σ : Fin 3 → Ground) (key : Ground) (r : Recipe 3) : Bool :=
  match r with
  | .ternary .penc k _ _ => normalizeRaw (k.subst σ) == key
  | .binary .mul a b => certificate σ key a && certificate σ key b
  | _ => match normalizeRaw (r.subst σ) with
    | .ternary .penc k _ (.const _) => chain r && k == key && 1 < r.nodeCount
    | _ => false

def catalogue (seed : Nat) : List (Recipe 3) :=
  let x : Recipe 3 := .name (40 + seed % 3)
  let y : Recipe 3 := .name (44 + seed % 3)
  let a : Recipe 3 := (Term.var 1).project (seed % 2)
  let b : Recipe 3 := (Term.var 2).project ((seed / 2) % 2)
  let c : Recipe 3 := .ternary .penc (.var 0) x y
  let prod := Term.binary .mul a b
  let mixed := Term.binary .mul c prod
  let pair := Term.binary .pair mixed (.binary .pair x y)
  let proof := Term.spk (.var 0) x y c
  let reveal := fun t : Recipe 3 => Term.unary .fst (.binary .pair t (.const .bottom))
  let seeds : List (Recipe 3) :=
    [.var 0, .var 1, .var 2, .const .zero, .const .one, .const .ok, .const .bottom,
     x, y, a, b, c, prod, mixed, pair, reveal pair, reveal mixed,
     .unary .snd pair, .binary .dec (.name 10) mixed,
     .binary .add y (.binary .add (.const .one) (.const .zero)),
     .binary .dec (.name 10) (.ternary .penc (.var 0) x pair),
     .binary .dec (.name 10) (.binary .mul a a),
     .binary .add (.const .one) (.const .one),
     (Term.var 1).project (2 + seed % 3), proof, reveal proof,
     .binary .dec (.name 10) (.ternary .penc (.var 0) x proof)]
  seeds.flatMap subterms

def originCheck (seed : Nat) : Bool :=
  let σ := (frame HistoricalFrameSPOT.names ((seed / 4) % 2 == 1) 0 1).value
  let entries := (catalogue seed).map (fun r => (r, normalizeRaw (r.subst σ)))
  entries.all (fun (r, value) =>
    entries.any (fun (s, other) => s.nodeCount < r.nodeCount && other == value) ||
    (match value with
      | .binary .pair _ _ => pairOrigin r
      | .ternary .penc key _ _ => certificate σ key r
      | .spk _ _ _ _ => proofOrigin r
      | _ => true))

#eval campaign "pair origins without minimum size (negative control)"
  (∀ n : Nat, pairOrigin (.unary .fst
    (.binary .pair (.binary .pair (.name n) (.name 44)) (.const .bottom))) = true) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "finite-catalogue minimum pair and ciphertext origins"
      (∀ n : Nat, originCheck n = true) seed
  unless (List.range 256).all originCheck do
    throw (IO.userError "minimum-origin backstop failed")
  IO.println "minimum-origin backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.MinimumOriginExperiments
