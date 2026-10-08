import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.RawNormalization

namespace ExplainableCrypto.Helios.Symbolic.MinimalRecipeExperiments
open ExplainableCrypto.Testing RewriteExperiments

/-- Each argument position of each arity, independently of the context lemmas. -/
def placements (a b c : Term Nat) : List (Context Nat) :=
  [.hole, .unary .pk .hole, .binaryLeft .pair .hole a,
   .binaryRight .dec a .hole, .ternaryFirst .penc .hole a b,
   .ternarySecond .penc a .hole b, .ternaryThird .checkspk a b .hole,
   .spkFirst .hole a b c, .spkSecond a .hole b c,
   .spkThird a b .hole c, .spkFourth a b c .hole]

def sizeCheck (seed : Nat) : Bool :=
  let a := generatedTerm (seed % 4) seed
  let b := generatedTerm (seed % 4) (seed + 13)
  (reductionPairs a b (.name 3) (.binary .add a b) (.const .one)).all fun (l, r) =>
    (placements a b (.name 5)).all fun ctx =>
      (ctx.fill (wrap (seed % 3) a r)).nodeCount <
        (ctx.fill (wrap (seed % 3) a l)).nodeCount

#eval campaign "one-node handle evaluation is raw normal (negative control)"
  (∀ n : Nat,
    let σ : Nat → Term Nat := fun _ => .unary .fst (.binary .pair (.name n) (.const .zero))
    normalizeRaw ((Term.var 0).subst σ) = (Term.var 0).subst σ) 1 true

#eval do
  for seed in [1, 7, 42] do
    campaign "raw rule size decrease in every argument position"
      (∀ n : Nat, sizeCheck n = true) seed
  unless (List.range 256).all sizeCheck do
    throw (IO.userError "minimal recipe size backstop failed")
  IO.println "minimal recipe size backstop: 256 inputs passed"

end ExplainableCrypto.Helios.Symbolic.MinimalRecipeExperiments
