import ExplainableCrypto.Helios.Symbolic.HistoricalFrameProtection

namespace ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT
open Historical

def names : Names 1 := ⟨10, 11, fun i j => 20 + 2 * i.val + j.val⟩

theorem fixture_names_fresh : names.Fresh := by
  unfold Names.Fresh Function.Injective
  decide

private def k : Ground := .unary .pk (.name 10)
private def c₀ : Ground := .ternary .penc k (.name 20) (.const .one)
private def c₁ : Ground := .ternary .penc k (.name 21) (.const .zero)
private def p₀ : Ground := .spk k (.name 20) (.const .one) c₀
private def p₁ : Ground := .spk k (.name 21) (.const .zero) c₁
private def aggregate : Ground := .spk k (.binary .compose (.name 20) (.name 21))
  (.binary .add (.const .one) (.const .zero)) (.binary .mul c₀ c₁)
private def expectedFields : List Ground := [c₀, c₁, p₀, p₁, aggregate]

/-- Literal oracle includes all three aggregate expressions and the source field order. -/
theorem two_candidate_fields : ballotFields names 0 0 = expectedFields := by decide

theorem two_world_assignments :
    (frame names false 0 1).value 1 = Term.tuple expectedFields ∧
    (frame names true 0 1).value 2 = ballot names 1 0 ∧
    (frame names false 0 1).value 1 ≠ (frame names true 0 1).value 1 := by decide

theorem aggregate_field_required {n : Nat} (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    (ballotFields ns i chosen).length ≠ 2 * (n + 1) := by
  rw [ballot_fields_length, fieldCount]
  omega

theorem public_key_handle (swap : Bool) :
    (Term.var 0 : Recipe 3).Public names.restricted ∧
    EqE ((frame names swap 0 1).eval (.var 0)) k := ⟨trivial, .refl _⟩

def firstCipher : Recipe 3 := .unary .fst (.var 1)

theorem public_ciphertext_projection : firstCipher.Public names.restricted ∧
    EqE ((frame names false 0 1).eval firstCipher) c₀ :=
  ⟨trivial, (RootStep.fst c₀ (Term.tuple [c₁, p₀, p₁, aggregate])).to_modulo.sound⟩

theorem both_worlds_nonce_excluded (swap : Bool) (r : Recipe 3) (hr : r.Public names.restricted)
    (rest : Ground) : ¬ EqE ((frame names swap 0 1).eval r) (.binary .compose (.name 20) rest) :=
  frame_nonce_composition_not_deducible names swap 0 1 r hr 0 0 rest

theorem both_worlds_key_excluded (swap : Bool) (r : Recipe 3) (hr : r.Public names.restricted) :
    ¬ EqE ((frame names swap 0 1).eval r) (.name 10) :=
  frame_secret_key_not_deducible names swap 0 1 r hr

def singletonNames : Names 0 := ⟨10, 11, fun i _ => 20 + i.val⟩

/-- The one-candidate boundary agrees with the earlier independently accepted fixture. -/
theorem singleton_ballot_agrees :
    ballot singletonNames 0 0 = oneCandidateBallot (.unary .pk (.name 10)) (.name 20) := by decide

theorem singleton_corrected_accepts :
    Accepted 0 (publicKey singletonNames) [] (ballot singletonNames 0 0) := by
  rw [singleton_ballot_agrees]
  exact oneCandidate_corrected_accepts _ _

theorem nonce_only_policy_allows_key_name :
    (Term.name 10 : Recipe 3).Public names.nonceNames ∧
    ¬ (Term.name 10 : Recipe 3).Public names.restricted := by
  unfold Term.Public
  decide

theorem nonce_only_recipes_excluded (swap : Bool) (r : Recipe 3)
    (hr : r.Public names.nonceNames) (rest : Ground) :
    ¬ EqE ((frame names swap 0 1).eval r) (.binary .compose (.name 20) rest) :=
  frame_nonce_composition_of_nonce_public names swap 0 1 r hr 0 0 rest

end ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT
