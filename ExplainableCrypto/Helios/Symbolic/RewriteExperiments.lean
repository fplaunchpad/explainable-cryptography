import ExplainableCrypto.Helios.Symbolic.RootReduction
import ExplainableCrypto.Testing.Plausible

namespace ExplainableCrypto.Helios.Symbolic.RewriteExperiments
open ExplainableCrypto.Testing

/-- Bounded arbitrary syntax, including nested destructors and non-ground variables. -/
def generatedTerm : Nat → Nat → Term Nat
  | 0, seed => match seed % 4 with
    | 0 => .const .zero | 1 => .const .one | 2 => .name seed | _ => .var seed
  | depth + 1, seed =>
    let a := generatedTerm depth (seed / 2)
    let b := generatedTerm depth (seed / 3 + 1)
    match seed % 9 with
    | 0 => .unary .fst a
    | 1 => .binary .pair a b
    | 2 => .binary .mul a b
    | 3 => .binary .add a b
    | 4 => .binary .compose a b
    | 5 => .ternary .penc a b (.const .one)
    | 6 => .binary .dec a b
    | 7 => .spk a b a b
    | _ => .ternary .checkspk a b a

/-- Every oriented source rule appears once; these are test fixtures, not a reducer. -/
def reductionPairs (k r s m n : Term Nat) : List (Term Nat × Term Nat) :=
  let c := Term.ternary .penc (.unary .pk k) r m
  let z := Term.ternary .penc k r (.const .zero)
  let o := Term.ternary .penc k r (.const .one)
  [(.unary .fst (.binary .pair m n), m),
   (.unary .snd (.binary .pair m n), n),
   (.binary .dec k c, m),
   (.binary .dec (.binary .partialDecrypt k c) c, m),
   (.binary .mul (.ternary .penc k r m) (.ternary .penc k s n),
     .ternary .penc k (.binary .compose r s) (.binary .add m n)),
   (.ternary .checkspk k z (.spk k r (.const .zero) z), .const .ok),
   (.ternary .checkspk k o (.spk k r (.const .one) o), .const .ok)]

def backgroundPairs (a b c : Term Nat) : List (Term Nat × Term Nat) :=
  [(.binary .add (.const .zero) (.const .one), .const .one),
   (.binary .add (.const .zero) (.const .zero), .const .zero)] ++
  [.mul, .add, .compose].flatMap (fun f =>
    [(.binary f a b, .binary f b a),
     (.binary f (.binary f a b) c, .binary f a (.binary f b c))])

/-- Directed nested contexts put the hole in several argument positions. -/
def wrap : Nat → Term Nat → Term Nat → Term Nat
  | 0, _, hole => hole
  | depth + 1, fixed, hole =>
    .spk fixed (.binary .pair (wrap depth fixed hole) fixed)
      (.const .zero) (.unary .pk fixed)

#eval campaign "tree size is not E0-invariant (negative control)"
  (∀ n : Nat, (Term.binary .add (.const .zero) (.const .zero) : Term Nat).nodeCount + n =
    (Term.const .zero : Term Nat).nodeCount + n) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "all seven reductions decrease contextual weight" (∀ n : Nat,
      let a := generatedTerm (n % 4) n
      let b := generatedTerm (n % 4) (n + 13)
      (reductionPairs a b (.name 3) (.binary .add a b) (.const .one)).all
        (fun (l, r) => (wrap (n % 4) b r).cryptoWeight <
          (wrap (n % 4) b l).cryptoWeight) = true) seed
    campaign "all eight E0 equations preserve contextual weight" (∀ n : Nat,
      let a := generatedTerm (n % 4) n
      let b := generatedTerm (n % 4) (n + 13)
      (backgroundPairs a b (.name 3)).all (fun (l, r) =>
        (wrap (n % 4) b l).cryptoWeight == (wrap (n % 4) b r).cryptoWeight) = true) seed

#eval do
  for seed in [1, 7, 42] do
    campaign "certified matcher recognises all seven rule families" (∀ n : Nat,
      let a := generatedTerm (n % 4) n
      let b := generatedTerm (n % 4) (n + 13)
      (reductionPairs a b (.name 3) (.binary .add a b) (.const .one)).all
        (fun (l, r) => (rootReduce l).map Subtype.val == some r) = true) seed

end ExplainableCrypto.Helios.Symbolic.RewriteExperiments
