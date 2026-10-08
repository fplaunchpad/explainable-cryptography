import ExplainableCrypto.Helios.Symbolic.NumericOffsetEquality
import ExplainableCrypto.Helios.Symbolic.StaticEquivalenceSPOT

namespace ExplainableCrypto.Helios.Symbolic.NumericReflectionSPOT
open Historical

/-- Fused enriched-frame ciphertext with one honest nonce and one public nonce. -/
def openCipher (payload : Term (Fin 2)) : Term (Fin 2) :=
  .ternary .penc (.unary .pk (.name 10)) (.binary .compose (.name 40) (.name 20))
    (.binary .add payload (.var 0))
abbrev left : Term (Fin 2) := openCipher (.name 41)
abbrev right : Term (Fin 2) := openCipher (.binary .add (.name 41) (.const .zero))
def votes (swap : Bool) (i : Fin 2) : Ground :=
  if i = 0 then .const (if swap then .one else .zero) else .const (if swap then .zero else .one)

/-- Prior to candidate substitution the extra zero is distinguished by E0. -/
theorem open_ciphertexts_not_baseEq : ¬ BaseEq left right := by
  intro he
  have hs := ((BaseEq.penc_iff _ _ _ _ _ _).mp he).2.2.add_summary
  have hn := congrArg AddSummary.numeric hs
  change (none : Option Nat) = some 0 at hn
  cases hn

private theorem padding_bit (p : Ground) (swap : Bool) :
    BaseEq (.binary .add p (.const (if swap then .one else .zero)))
      (.binary .add (.binary .add p (.const .zero)) (.const (if swap then .one else .zero))) := by
  cases swap with
  | false => exact BaseEq.zero_padding_after_number p 0
  | true =>
    have h := BaseEq.zero_padding_after_number p 1
    have h₁ : BaseEq (.binary .add p (addNumeral 1)) (.binary .add p (.const .one)) :=
      .binary .add (.refl _) (.equation .zero_one)
    have h₂ : BaseEq (.binary .add (.binary .add p (.const .zero)) (addNumeral 1))
        (.binary .add (.binary .add p (.const .zero)) (.const .one)) :=
      .binary .add (.refl _) (.equation .zero_one)
    exact h₁.symm.trans (h.trans h₂)

/-- Both candidate substitutions make the enriched ciphertext values E0-equal. -/
theorem substituted_ciphertexts_baseEq (swap : Bool) :
    BaseEq (left.subst (votes swap)) (right.subst (votes swap)) :=
  .ternary .penc (.refl _) (.refl _) (padding_bit (.name 41) swap)

/-- A permanent counterexample to reflecting equality to open vote variables. -/
theorem open_equality_reflection_false :
    (∀ swap : Bool, BaseEq (left.subst (votes swap)) (right.subst (votes swap))) ∧
      ¬ BaseEq left right := ⟨substituted_ciphertexts_baseEq, open_ciphertexts_not_baseEq⟩

abbrev names : Names 0 := BallotValueSPOT.names
abbrev abstain : CandidateSubstitution 0 Empty := (BitCandidate.abstain 0).substitution
abbrev selected : CandidateSubstitution 0 Empty := (BitCandidate.selected (0 : Fin 1)).substitution

def productRecipe (payload : Recipe 3) : Recipe 3 :=
  .binary .mul (.ternary .penc (.var 0) (.name 40) payload) ((Term.var 1).project 0)

theorem fixture_names_fresh : names.Fresh := by
  unfold Names.Fresh Function.Injective
  decide

theorem public_product_recipes :
    (productRecipe (.name 41)).Public names.restricted ∧
      (productRecipe (.binary .add (.name 41) (.const .zero))).Public names.restricted := by
  change ((True ∧ 40 ∉ names.restricted ∧ 41 ∉ names.restricted) ∧ True) ∧
    ((True ∧ 40 ∉ names.restricted ∧ (41 ∉ names.restricted ∧ True)) ∧ True)
  decide

private theorem product_value (swap : Bool) (payload : Ground) (r : Recipe 3)
    (hr : (General.frame names swap abstain selected).eval r = payload) :
    EqE ((General.frame names swap abstain selected).eval (productRecipe r))
      (.ternary .penc (.unary .pk (.name 10)) (.binary .compose (.name 40) (.name 20))
        (.binary .add payload (.const (if swap then .one else .zero)))) := by
  have hc : EqE ((General.frame names swap abstain selected).eval ((Term.var 1).project 0))
      (General.ciphertext names 0 (General.choice swap abstain selected 0).value 0) := by
    simpa [Frame.eval, Term.subst_project, Term.subst, General.frame] using
      General.ballot_project_ciphertext names 0 (General.choice swap abstain selected 0).value 0
  change EqE (.binary .mul (.ternary .penc (publicKey names) (.name 40)
    ((General.frame names swap abstain selected).eval r))
    ((General.frame names swap abstain selected).eval ((Term.var 1).project 0))) _
  rw [hr]
  have hprod := (EqE.binary .mul (EqE.refl (.ternary .penc (publicKey names) (.name 40) payload)) hc).trans
    (RootStep.homomorphic _ _ _ _ _).sound
  cases swap <;> exact hprod

/-- The two fused templates really arise from permitted recipes in the fresh
source frame; they are equal in both worlds, not a privacy distinguisher. -/
theorem public_products_equal_both_worlds (swap : Bool) :
    EqE ((General.frame names swap abstain selected).eval (productRecipe (.name 41)))
      ((General.frame names swap abstain selected).eval
        (productRecipe (.binary .add (.name 41) (.const .zero)))) := by
  have hL := product_value swap (.name 41) (.name 41) rfl
  have hR := product_value swap (.binary .add (.name 41) (.const .zero))
    (.binary .add (.name 41) (.const .zero)) rfl
  exact hL.trans ((substituted_ciphertexts_baseEq swap).sound.trans hR.symm)

/-- Adding one instead of zero still changes the public payload comparison. -/
theorem positive_increment_not_erased (k : Nat) :
    ¬ BaseEq (Term.binary .add (.name 41) (addNumeral (V := Empty) k))
      (.binary .add (.binary .add (.name 41) (.const .one)) (addNumeral k)) := by
  intro he
  have hs := he.add_summary
  simp only [Term.addSummary, addNumeral_summary] at hs
  have hn := (AddSummary.combine_number_eq_iff _ _ k).mp hs |>.2
  change 0 = 1 at hn
  omega

/-- Full-E cancellation tolerates a reducible public payload and a different
zero-padded representative on the other side. -/
theorem reducible_payload_offset (k : Nat) :
    EqE (Term.binary .add (.unary .fst (.binary .pair (.name 41) (.const .bottom)))
      (addNumeral (V := Empty) k))
      (.binary .add (.binary .add (.name 41) (.const .zero)) (addNumeral k)) := by
  apply (EqE.add_numeric_offset_iff _ _ 0 k).mp
  exact (EqE.binary .add (RootStep.fst (.name 41) (.const .bottom)).sound (.refl _)).trans
    (BaseEq.zero_padding_after_number (.name 41) 0).sound

end ExplainableCrypto.Helios.Symbolic.NumericReflectionSPOT
