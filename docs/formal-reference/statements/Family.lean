structure Family (q : Nat → Nat) (G : Nat → Type)
    [∀ n, Fact (q n).Prime] [∀ n, AddCommGroup (G n)]
    [∀ n, Module (ZMod (q n)) (G n)] [∀ n, DecidableEq (G n)] where
  representation : GroupRepresentation G
  scalarWidth : Polynomial Nat
  scalar_width : ∀ n, (q n).size ≤ scalarWidth.eval n
  fingerprintWidth : Polynomial Nat
  fingerprint : ∀ n, PublicParameters (ZMod (q n)) (G n) → Nat
  fingerprint_width : ∀ n parameters,
    parameters.candidates = [0, 1] → parameters.eligibleVoters = [0, 1, 2] →
      (fingerprint n parameters).size ≤ fingerprintWidth.eval n
  generator : ∀ n, G n
  generator_injective : ∀ n,
    Function.Injective (fun r : ZMod (q n) => r • generator n)
  Init : Nat → Type
  Saved : Nat → Type
  encodeInit : ∀ n, Init n → List Bool
  encodeSaved : ∀ n, Saved n → List Bool
  init_injective : ∀ n, Function.Injective (encodeInit n)
  saved_injective : ∀ n, Function.Injective (encodeSaved n)
  prepare : ∀ n, Comp (ZMod (q n)) (G n) (Init n)
  adversary : ∀ n, Init n → Adversary (ZMod (q n)) (G n) (Saved n)
  prepareCost : Polynomial Nat
  initGrowth : Polynomial Nat
  castCost : Polynomial Nat
  savedGrowth : Polynomial Nat
  guessCost : Polynomial Nat
  prepare_queries : ∀ n, (prepare n).IsTotalQueryBound (prepareCost.eval n)
  prepare_size : ∀ n initial, initial ∈ support (prepare n) →
    (encodeInit n initial).length ≤ initGrowth.eval n
  cast_queries : ∀ n initial before,
    ((adversary n initial).castBallot before).IsTotalQueryBound
      (castCost.eval (n + (encodeInit n initial).length +
        prefixInputWidth representation n before))
  cast_size : ∀ n initial before output,
    output ∈ support ((adversary n initial).castBallot before) →
    (encodeSaved n output.2).length ≤ savedGrowth.eval
      (n + (encodeInit n initial).length +
        prefixInputWidth representation n before)
  guess_queries : ∀ n initial saved view,
    ((adversary n initial).guessVote saved view).IsTotalQueryBound
      (guessCost.eval (n + (encodeInit n initial).length + (encodeSaved n saved).length +
        resultInputWidth representation n view))
