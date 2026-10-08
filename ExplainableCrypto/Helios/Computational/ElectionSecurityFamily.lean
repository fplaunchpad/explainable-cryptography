import ExplainableCrypto.Helios.Computational.ElectionPublicBounds
import ExplainableCrypto.Helios.Computational.ElectionPublicEncoding
import ExplainableCrypto.Helios.Computational.ElectionClock
import ExplainableCrypto.Helios.Computational.ElectionSecrecyConditional

/-!
Coverage of encoded, input-bounded oracle attackers for the fixed election.

Query bounds and private output growth are properties of the original callbacks,
over all typed oracle replies. They are not assumptions of game correspondence.
The game-side public bounds and query-clock transparency derive that correspondence.
The connection from uniform PPT implementations to this resource interface is an
external size/time argument, documented with the outcome of this bounded experiment.
-/
namespace ExplainableCrypto.Helios.Computational.ElectionSecurityFamily
open OracleComp OracleSpec ElectionOracle ElectionPublicBounds
open ReductionEfficiency


variable {q : Nat → Nat} [∀ n, Fact (q n).Prime] {G : Nat → Type}
  [∀ n, AddCommGroup (G n)] [∀ n, Module (ZMod (q n)) (G n)]
  [∀ n, DecidableEq (G n)]

/-- Public scalars use canonical binary representatives; the modulus width is
an explicit parameter policy, independent of inverse-field-size negligibility. -/
def scalarSize (n : Nat) (x : ZMod (q n)) : Nat := x.val.size

def scalarEncode (n : Nat) (x : ZMod (q n)) : List Bool := x.val.bits

def prefixInputWidth (representation : GroupRepresentation G) (n : Nat)
    (before : PublicPrefix (ZMod (q n)) (G n)) : Nat :=
  (ElectionPublicEncoding.encodePrefix (representation.encode n) (scalarEncode n) before).length

def resultInputWidth (representation : GroupRepresentation G) (n : Nat)
    (view : PublicResult (ZMod (q n)) (G n)) : Nat :=
  (ElectionPublicEncoding.encodeResult (representation.encode n) (scalarEncode n) view).length

/-- This interface states local callback resource properties. In particular,
private sizes are lengths of injective encodings, not arbitrary numeric measures.
Pure output growth is bounded separately from the number of oracle queries. -/
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

/-- Natural-coefficient polynomials are monotone on natural inputs. -/
theorem eval_mono (P : Polynomial Nat) {a b : Nat} (h : a ≤ b) : P.eval a ≤ P.eval b := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h k)

namespace Family
variable (A : Family q G)

noncomputable def leafBound : Polynomial Nat :=
  A.representation.width + A.scalarWidth + A.fingerprintWidth + 1

noncomputable def prefixPolynomial : Polynomial Nat := 100 * (A.leafBound + 1)
noncomputable def resultPolynomial : Polynomial Nat := A.prefixPolynomial + 1000 * (A.leafBound + 1)
noncomputable def castInput : Polynomial Nat := Polynomial.X + A.initGrowth + 100000000 * A.prefixPolynomial
noncomputable def castCap : Polynomial Nat := A.castCost.comp A.castInput
noncomputable def savedCap : Polynomial Nat := A.savedGrowth.comp A.castInput
noncomputable def guessInput : Polynomial Nat :=
  Polynomial.X + A.initGrowth + A.savedCap + 10000000000 * A.resultPolynomial
noncomputable def guessCap : Polynomial Nat := A.guessCost.comp A.guessInput

theorem group_bound (n : Nat) (g : G n) :
    (A.representation.encode n g).length ≤ A.leafBound.eval n := by
  have h := A.representation.width_bound n g
  simp only [leafBound, Polynomial.eval_add, Polynomial.eval_one]
  omega

theorem scalar_bound (n : Nat) (x : ZMod (q n)) :
    scalarSize n x ≤ A.leafBound.eval n := by
  have h := Nat.size_le_size (Nat.le_of_lt x.val_lt)
  have hw := A.scalar_width n
  simp only [scalarSize, leafBound, Polynomial.eval_add, Polynomial.eval_one]
  omega

theorem fingerprint_bound (n : Nat) (parameters : PublicParameters (ZMod (q n)) (G n))
    (hc : parameters.candidates = [0, 1]) (he : parameters.eligibleVoters = [0, 1, 2]) :
    (A.fingerprint n parameters).size ≤ A.leafBound.eval n := by
  have h := A.fingerprint_width n parameters hc he
  simp only [leafBound, Polynomial.eval_add, Polynomial.eval_one]
  omega

/-- The actual serialized lengths, including nested framing, are bounded by
the structural measures. No serialization-size correspondence is assumed. -/
theorem prefix_encoded_le (n : Nat) (before : PublicPrefix (ZMod (q n)) (G n)) :
    prefixInputWidth A.representation n before ≤ 100000000 *
      prefixWidth (fun g => (A.representation.encode n g).length) (scalarSize n) before := by
  unfold prefixInputWidth scalarSize
  simpa only [scalarEncode, Nat.size_eq_bits_len] using
    ElectionPublicEncoding.prefix_length_le (A.representation.encode n) (scalarEncode n) before

theorem result_encoded_le (n : Nat) (view : PublicResult (ZMod (q n)) (G n)) :
    resultInputWidth A.representation n view ≤ 10000000000 *
      resultWidth (fun g => (A.representation.encode n g).length) (scalarSize n) view := by
  unfold resultInputWidth scalarSize
  simpa only [scalarEncode, Nat.size_eq_bits_len] using
    ElectionPublicEncoding.result_length_le (A.representation.encode n) (scalarEncode n) view

theorem prefix_encoding_injective (n : Nat) :
    Function.Injective (ElectionPublicEncoding.encodePrefix
      (A.representation.encode n) (scalarEncode (q := q) n)) :=
  ElectionPublicEncoding.prefix_injective (A.representation.injective n)
    (ElectionPublicEncoding.scalar_bits_injective (q n))

theorem result_encoding_injective (n : Nat) :
    Function.Injective (ElectionPublicEncoding.encodeResult
      (A.representation.encode n) (scalarEncode (q := q) n)) :=
  ElectionPublicEncoding.result_injective (A.representation.injective n)
    (ElectionPublicEncoding.scalar_bits_injective (q n))

theorem cast_bounded (n : Nat) (initial : A.Init n) (before : PublicPrefix (ZMod (q n)) (G n))
    (hi : (A.encodeInit n initial).length ≤ A.initGrowth.eval n)
    (hb : prefixWidth (fun g => (A.representation.encode n g).length) (scalarSize n) before ≤
      A.prefixPolynomial.eval n) :
    ((A.adversary n initial).castBallot before).IsTotalQueryBound (A.castCap.eval n) := by
  apply (A.cast_queries n initial before).mono
  have he := (A.prefix_encoded_le n before).trans (Nat.mul_le_mul_left 100000000 hb)
  simp only [castCap, Polynomial.eval_comp, castInput, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_ofNat]
  exact eval_mono _ (by omega)

theorem saved_bounded (n : Nat) (initial : A.Init n) (before : PublicPrefix (ZMod (q n)) (G n))
    (hi : (A.encodeInit n initial).length ≤ A.initGrowth.eval n)
    (hb : prefixWidth (fun g => (A.representation.encode n g).length) (scalarSize n) before ≤
      A.prefixPolynomial.eval n)
    (output : Ballot (ZMod (q n)) (G n) 2 × A.Saved n)
    (ho : output ∈ support ((A.adversary n initial).castBallot before)) :
    (A.encodeSaved n output.2).length ≤ A.savedCap.eval n := by
  apply (A.cast_size n initial before output ho).trans
  have he := (A.prefix_encoded_le n before).trans (Nat.mul_le_mul_left 100000000 hb)
  simp only [savedCap, Polynomial.eval_comp, castInput, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_ofNat]
  exact eval_mono _ (by omega)

theorem guess_bounded (n : Nat) (initial : A.Init n) (saved : A.Saved n)
    (view : PublicResult (ZMod (q n)) (G n))
    (hi : (A.encodeInit n initial).length ≤ A.initGrowth.eval n)
    (hs : (A.encodeSaved n saved).length ≤ A.savedCap.eval n)
    (hv : resultWidth (fun g => (A.representation.encode n g).length) (scalarSize n) view ≤
      A.resultPolynomial.eval n) :
    ((A.adversary n initial).guessVote saved view).IsTotalQueryBound (A.guessCap.eval n) := by
  apply (A.guess_queries n initial saved view).mono
  have he := (A.result_encoded_le n view).trans (Nat.mul_le_mul_left 10000000000 hv)
  simp only [guessCap, Polynomial.eval_comp, guessInput, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_ofNat]
  exact eval_mono _ (by omega)

/-- Actual source prefixes satisfy the public bound under every typed reply,
including inconsistent replies that a cached execution would never produce. -/
theorem prefix_bounded (n : Nat) (secret keyNonce : ZMod (q n)) (vote : Bool)
    (alice bob : HonestCoins (ZMod (q n))) (before : PublicPrefix (ZMod (q n)) (G n))
    (ho : before ∈ support (prefixWithCoins (A.fingerprint n) (A.generator n)
      secret keyNonce vote alice bob)) :
    prefixWidth (fun g => (A.representation.encode n g).length) (scalarSize n) before ≤
      A.prefixPolynomial.eval n ∧ before.board.length ≤ 2 := by
  simpa only [prefixPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_add, Polynomial.eval_one, prefixBound] using
    support_prefix_width (fun g => (A.representation.encode n g).length) (scalarSize n)
      (A.leafBound.eval n) (A.group_bound n) (A.scalar_bound n)
      (A.fingerprint n) (A.fingerprint_bound n) (A.generator n)
      secret keyNonce vote alice bob before ho

theorem prefix_input_bounded (n : Nat) (secret keyNonce : ZMod (q n)) (vote : Bool)
    (alice bob : HonestCoins (ZMod (q n))) (before : PublicPrefix (ZMod (q n)) (G n))
    (ho : before ∈ support (prefixWithCoins (A.fingerprint n) (A.generator n)
      secret keyNonce vote alice bob)) :
    prefixInputWidth A.representation n before ≤ (100000000 * A.prefixPolynomial).eval n := by
  simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat] using
    (A.prefix_encoded_le n before).trans (Nat.mul_le_mul_left 100000000
      (A.prefix_bounded n secret keyNonce vote alice bob before ho).1)

theorem result_bounded (n : Nat) (secret : ZMod (q n)) (nonces : Fin 2 → ZMod (q n))
    (before : PublicPrefix (ZMod (q n)) (G n))
    (hp : prefixWidth (fun g => (A.representation.encode n g).length) (scalarSize n) before ≤
      A.prefixPolynomial.eval n) (hb : before.board.length ≤ 2)
    (submission : Ballot (ZMod (q n)) (G n) 2) (view : PublicResult (ZMod (q n)) (G n))
    (ho : view ∈ support (finishWithCoins secret nonces before submission)) :
    resultWidth (fun g => (A.representation.encode n g).length) (scalarSize n) view ≤
      A.resultPolynomial.eval n := by
  simpa only [resultPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_one, resultBound] using
    (finish_width_le (fun g => (A.representation.encode n g).length) (scalarSize n)
      (A.leafBound.eval n) (A.prefixPolynomial.eval n) (A.group_bound n) (A.scalar_bound n)
      secret nonces before hp hb submission view ho).1

theorem result_input_bounded (n : Nat) (secret keyNonce : ZMod (q n)) (vote : Bool)
    (alice bob : HonestCoins (ZMod (q n))) (before : PublicPrefix (ZMod (q n)) (G n))
    (hp : before ∈ support (prefixWithCoins (A.fingerprint n) (A.generator n)
      secret keyNonce vote alice bob)) (nonces : Fin 2 → ZMod (q n))
    (submission : Ballot (ZMod (q n)) (G n) 2) (view : PublicResult (ZMod (q n)) (G n))
    (hv : view ∈ support (finishWithCoins secret nonces before submission)) :
    resultInputWidth A.representation n view ≤ (10000000000 * A.resultPolynomial).eval n := by
  obtain ⟨hw, hb⟩ := A.prefix_bounded n secret keyNonce vote alice bob before hp
  simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat] using
    (A.result_encoded_le n view).trans (Nat.mul_le_mul_left 10000000000
      (A.result_bounded n secret nonces before hw hb submission view hv))

/-- The clocked family is globally bounded even on inputs never reached by the game.
Option-tagged saved state supplies a total fallback without assuming a private default. -/
noncomputable def prepared : ElectionSecrecyPrototype.PreparedFamily (fun n => ZMod (q n)) G where
  Init := A.Init
  Saved n := Option (A.Saved n)
  fingerprint := A.fingerprint
  generator := A.generator
  generator_injective := A.generator_injective
  prepare := A.prepare
  adversary n initial := ElectionClock.adversary (A.castCap.eval n) (A.guessCap.eval n)
    (A.adversary n initial)
  p n := A.prepareCost.eval n
  c n := A.castCap.eval n
  prepare_hash n := (A.prepare_queries n).isQueryBoundP
  cast_hash _n _initial before := ElectionClock.cast_hash_bound _ _ _ before

theorem world_eq (n : Nat) (initial : A.Init n)
    (hi : initial ∈ support (A.prepare n)) (vote : Bool) :
    world (A.fingerprint n) (A.generator n) (A.prepared.adversary n initial) vote =
      world (A.fingerprint n) (A.generator n) (A.adversary n initial) vote := by
  apply ElectionClock.world_eq
  · intro secret keyNonce alice bob before hb
    exact A.cast_bounded n initial before (A.prepare_size n initial hi)
      (A.prefix_bounded n secret keyNonce vote alice bob before hb).1
  · intro secret keyNonce alice bob before hb submission saved hs nonces view hv
    obtain ⟨hwidth, hboard⟩ := A.prefix_bounded n secret keyNonce vote alice bob before hb
    have hinit := A.prepare_size n initial hi
    exact A.guess_bounded n initial saved view hinit
      (A.saved_bounded n initial before hinit hwidth (submission, saved) hs)
      (A.result_bounded n secret nonces before hwidth hboard submission view hv)

/-- Coverage is an equality of complete oracle computations, with the same
preparation and persistent handler. It is not a caller-supplied simulation premise. -/
theorem coverage (n : Nat) :
    preparedGame (A.fingerprint n) (A.generator n) (A.prepared.prepare n)
      (A.prepared.adversary n) =
    preparedGame (A.fingerprint n) (A.generator n) (A.prepare n) (A.adversary n) := by
  unfold preparedGame
  change (A.prepare n >>= _) = (A.prepare n >>= _)
  apply bind_congr_of_forall_mem_support
  intro initial hi
  unfold game
  apply bind_congr
  intro vote
  rw [A.world_eq n initial hi vote]

/-- Full shared-cache output law, preserving the actual handler and its final cache. -/
theorem run_coverage (n : Nat) (cache : ElectionOracle.Cache (ZMod (q n)) (G n)) :
    ElectionOracle.run (preparedGame (A.fingerprint n) (A.generator n)
      (A.prepared.prepare n) (A.prepared.adversary n)) cache =
    ElectionOracle.run (preparedGame (A.fingerprint n) (A.generator n)
      (A.prepare n) (A.adversary n)) cache := by rw [A.coverage]

noncomputable def bias (n : Nat) : ℝ :=
  |(Pr[fun out => out.1 = true | ElectionOracle.run
    (preparedGame (A.fingerprint n) (A.generator n) (A.prepare n) (A.adversary n)) ∅]).toReal - 1/2|

theorem bias_eq (n : Nat) : ElectionSecrecyPrototype.bias A.prepared n = A.bias n := by
  unfold ElectionSecrecyPrototype.bias bias
  change |(Pr[fun out => out.1 = true | ElectionOracle.run
    (preparedGame (A.fingerprint n) (A.generator n)
      (A.prepared.prepare n) (A.prepared.adversary n)) ∅]).toReal - 1/2| = _
  rw [A.run_coverage]

/-- Secrecy of the original input-bounded attacker. The two efficiency hypotheses
refer to the exact normalized family: game equality alone does not transfer
efficiency through the extractor's altered replay paths. -/
theorem ballot_secrecy
    (hsize : negligible (fun n => noncePointBound (ZMod (q n))))
    (hmain : MainReductionEfficient A.prepared A.representation)
    (hreject : RejectionReductionEfficient A.prepared A.representation)
    (hddh : DDHAssumption (q := q) A.representation A.generator) :
    negligible (fun n => ENNReal.ofReal (A.bias n)) := by
  have h := ElectionSecrecyConditional.prepared_negligible_of_native_coin_ddh
    A.prepared A.representation (A.prepareCost + A.castCap)
    (A.prepareCost + A.castCap + A.guessCap)
    (fun n => by simp [prepared, Polynomial.eval_add]) hsize
    (fun n => A.prepareCost.eval n) (fun n => A.castCap.eval n) (fun n => A.guessCap.eval n)
    (fun n => by simp [Polynomial.eval_add])
    A.prepare_queries
    (fun n initial before => ElectionClock.cast_bound _ _ _ before)
    (fun n initial saved view => ElectionClock.guess_bound _ _ _ saved view)
    hmain hreject hddh
  simpa only [A.bias_eq] using h

#print axioms coverage
#print axioms run_coverage
#print axioms bias_eq
#print axioms ballot_secrecy

end Family
export Family (coverage ballot_secrecy)

end ExplainableCrypto.Helios.Computational.ElectionSecurityFamily
