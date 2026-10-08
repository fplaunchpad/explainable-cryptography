import ExplainableCrypto.Helios.Computational.RepairedSubmissionCost
import ExplainableCrypto.Helios.Computational.ScalarCodec

/-! Explicit historical nonce enumeration and reuse of pinned scalar sampling.
Uniform range draws are still unifSpec primitives, not fair-bit machine code. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

variable {q : Nat} [Fact q.Prime]

/-- Index i denotes the nonzero residue i+1. No unit enumeration is executed. -/
def primeNonceValue (i : Fin (q-1)) : ZMod q := (i.val+1 : Nat)

private theorem primeNonceValue_val (i : Fin (q-1)) :
    (primeNonceValue i).val = i.val+1 := by
  apply ZMod.val_natCast_of_lt
  have := i.isLt
  omega

private theorem primeNonceValue_ne_zero (i : Fin (q-1)) : primeNonceValue i ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [primeNonceValue_val,ZMod.val_zero] at hv
  omega

/-- The unit structure is used only to prove distribution correspondence. -/
def primeNonceEquiv : Fin (q-1) ≃ (ZMod q)ˣ where
  toFun i := Units.mk0 (primeNonceValue i) (primeNonceValue_ne_zero i)
  invFun u := ⟨(u.val : ZMod q).val-1,by
    have hlt := (u.val : ZMod q).val_lt
    have hz : (u.val : ZMod q).val ≠ 0 := by
      intro h
      apply Units.ne_zero u
      apply ZMod.val_injective q
      simpa only [ZMod.val_zero] using h
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp only [Units.val_mk0,primeNonceValue_val]
    omega
  right_inv u := by
    apply Units.ext
    apply ZMod.val_injective q
    rw [Units.val_mk0,primeNonceValue_val]
    have hz : (u.val : ZMod q).val ≠ 0 := by
      intro h
      apply Units.ne_zero u
      apply ZMod.val_injective q
      simpa only [ZMod.val_zero] using h
    change (u.val : ZMod q).val-1+1 = (u.val : ZMod q).val
    omega

private theorem primeNonceEquiv_val (i : Fin (q-1)) :
    (primeNonceEquiv i).val = primeNonceValue i := rfl

/-- Use the native Fin sampler and an explicit successor/cast map. -/
def samplePrimeNonzero : ProbComp (ZMod q) :=
  haveI : NeZero (q-1) := ⟨by have := (Fact.out : q.Prime).two_le; omega⟩
  primeNonceValue <$> uniformSample (Fin (q-1))

/-- The explicit sampler and the historical sampler agree at every residue. -/
theorem samplePrimeNonzero_probability (r : ZMod q) :
    Pr[= r | samplePrimeNonzero] = Pr[= r | sampleNonzero (ZMod q)] := by
  classical
  let : NeZero (q-1) := ⟨by have := (Fact.out : q.Prime).two_le; omega⟩
  have hi : Function.Injective (primeNonceValue (q := q)) := by
    intro i j h
    apply (primeNonceEquiv (q := q)).injective
    apply Units.ext
    exact h
  by_cases hz : r = 0
  · subst r
    have hn : (0 : ZMod q) ∉ support (sampleNonzero (ZMod q)) :=
      fun h => sampleNonzero_ne_zero h rfl
    have he : (0 : ZMod q) ∉ support samplePrimeNonzero := by
      simp only [samplePrimeNonzero,support_map,Set.mem_image]
      rintro ⟨i,_,h⟩
      exact primeNonceValue_ne_zero i h
    have he' : Pr[= (0 : ZMod q) | samplePrimeNonzero] = 0 := by
      simpa only [probOutput_eq_zero_iff] using he
    have hn' : Pr[= (0 : ZMod q) | sampleNonzero (ZMod q)] = 0 := by
      simpa only [probOutput_eq_zero_iff] using hn
    exact he'.trans hn'.symm
  · let u := Units.mk0 r hz
    obtain ⟨i,he⟩ := (primeNonceEquiv (q := q)).surjective u
    have hr : primeNonceValue i = r := congrArg Units.val he
    rw [← hr]
    unfold samplePrimeNonzero
    rw [probOutput_map_injective _ hi]
    have hp := sampleNonzero_probability (primeNonceEquiv (q := q) i)
    simpa only [primeNonceEquiv_val,probOutput_uniformSample,Fintype.card_fin,
      ZMod.card] using hp.symm

/-- Every subsequent probabilistic computation retains its full distribution. -/
theorem samplePrimeNonzero_bind {A : Type} (k : ZMod q → ProbComp A) (x : A) :
    Pr[= x | samplePrimeNonzero >>= k] = Pr[= x | sampleNonzero (ZMod q) >>= k] := by
  simp only [probOutput_bind_eq_tsum,samplePrimeNonzero_probability]

def drawPrimeNoncePair : ProbComp (ZMod q × ZMod q) := do
  let r0 ← samplePrimeNonzero
  let r1 ← samplePrimeNonzero
  pure (r0,r1)

/-- Preserve independence as well as both nonce marginals, for arbitrary uses. -/
theorem drawPrimeNoncePair_bind {A : Type} (k : ZMod q × ZMod q → ProbComp A) (x : A) :
    Pr[= x | drawPrimeNoncePair >>= k] = Pr[= x | drawNoncePair (ZMod q) >>= k] := by
  simp only [drawPrimeNoncePair,drawNoncePair,bind_assoc,pure_bind]
  rw [samplePrimeNonzero_bind]
  apply probOutput_bind_congr
  intro r hr
  exact samplePrimeNonzero_bind _ _

/-- The existing pinned FinEnum scalar sampler already uses one uniform query. -/
theorem primeScalarSampler_total_bound :
    (uniformSample (ZMod q)).IsTotalQueryBound 1 := by
  change ((ZMod.finEquiv q) <$> uniformSample (Fin q)).IsTotalQueryBound 1
  apply (isQueryBound_map_iff _ _ 1 _ _).mpr
  cases q with
  | zero => exact (Nat.not_prime_zero Fact.out).elim
  | succ n => exact ⟨by norm_num,fun _ => trivial⟩

/-- The explicit nonzero sampler also uses at most one uniform-index query. -/
theorem samplePrimeNonzero_total_bound : samplePrimeNonzero (q := q) |>.IsTotalQueryBound 1 := by
  let : NeZero (q-1) := ⟨by have := (Fact.out : q.Prime).two_le; omega⟩
  unfold samplePrimeNonzero
  apply (isQueryBound_map_iff _ _ 1 _ _).mpr
  have hf (n : Nat) [NeZero n] : (uniformSample (Fin n)).IsTotalQueryBound 1 := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact ⟨by norm_num,fun _ => trivial⟩
  exact hf _

variable {G : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]

attribute [local irreducible] repairedSubmission_joint_extract

/-- Apply the existing interaction theorem with VCVio's computable ZMod sampler;
no ofFintype sampler substitution or caller sampler-cost hypothesis is needed. -/
theorem repairedSubmission_joint_extract_prime_total_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n m : Nat) (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    (repairedSubmission_joint_extract g pk vote attacker n).IsTotalQueryBound (16*(m+19)) :=
  repairedSubmission_joint_extract_total_query_bound g pk vote attacker n m
    primeScalarSampler_total_bound hb

#print axioms samplePrimeNonzero_probability
#print axioms samplePrimeNonzero_bind
#print axioms drawPrimeNoncePair_bind
#print axioms primeScalarSampler_total_bound
#print axioms samplePrimeNonzero_total_bound
#print axioms repairedSubmission_joint_extract_prime_total_bound
end ExplainableCrypto.Helios.Computational
