import ExplainableCrypto.Helios.Symbolic.CiphertextProducts
import ExplainableCrypto.Helios.Symbolic.SmallRecipeBounds
import ExplainableCrypto.Helios.Symbolic.HistoricalFrameProtection
import ExplainableCrypto.Helios.Symbolic.HistoricalValidity
import Mathlib.Tactic.FinCases

namespace ExplainableCrypto.Helios.Symbolic

theorem Term.subst_drop {V W : Type} (σ : V → Term W) (n : Nat) (t : Term V) :
    (t.drop n).subst σ = (t.subst σ).drop n := by
  induction n generalizing t <;> simp_all [Term.drop, Term.subst]

theorem Term.subst_project {V W : Type} (σ : V → Term W) (n : Nat) (t : Term V) :
    (t.project n).subst σ = (t.subst σ).project n := by
  simp [Term.project, Term.subst, Term.subst_drop]

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical

private theorem ballot_pair_shape {n : Nat} (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    ∃ a b, ballot ns i chosen = .binary .pair a b := by
  have hl := ballot_fields_length ns i chosen
  cases he : ballotFields ns i chosen with
  | nil => simp only [he, List.length_nil, fieldCount] at hl; omega
  | cons a xs => exact ⟨a, Term.tuple xs, by simp [ballot, he, Term.tuple]⟩

/-- Every initial handle exposes a key or whole ballot, never a ciphertext value. -/
theorem frame_handle_not_ciphertext {n : Nat} (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (v : Fin 3) (k r m : Ground) :
    ¬ EqE ((frame ns swap left right).value v) (.ternary .penc k r m) := by
  dsimp [frame]
  split_ifs
  · exact pk_not_eqE_penc _ _ _ _
  · obtain ⟨a, b, hb⟩ := ballot_pair_shape ns 0 (choice swap left right 0)
    rw [hb]
    exact fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) k r m a b h.symm
  · obtain ⟨a, b, hb⟩ := ballot_pair_shape ns 1 (choice swap left right 1)
    rw [hb]
    exact fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) k r m a b h.symm

/-- The bound covers arbitrary recipes and all names, independently of publicness. -/
theorem frame_ciphertext_recipe_size_bound {n : Nat} (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (recipe : Recipe 3) (k r m : Ground)
    (he : EqE ((frame ns swap left right).eval recipe) (.ternary .penc k r m)) :
    2 ≤ recipe.nodeCount :=
  ciphertext_recipe_size_ge_two _ k r m
    (fun v => frame_handle_not_ciphertext ns swap left right v k r m) he

/-- Any recipe E-equal to an honest component supplies a constant product leaf.
The size premise is proved from the actual frame, not required from the caller. -/
theorem honest_component_product {n : Nat} (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (recipe : Recipe 3) (i : Fin 2) (j : Fin (n + 1))
    (he : EqE ((frame ns swap left right).eval recipe)
      (ciphertext ns i (choice swap left right i) j)) :
    CiphertextProduct (frame ns swap left right).value (publicKey ns) recipe
      (.const (if j = choice swap left right i then .one else .zero)) (.name (ns.nonce i j)) := by
  apply CiphertextProduct.constant _ _ _ he
  have hs := frame_ciphertext_recipe_size_bound ns swap left right recipe _ _ _ he
  omega

theorem frame_voter_handle {n : Nat} (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (i : Fin 2) :
    (frame ns swap left right).value i.succ = ballot ns i (choice swap left right i) := by
  fin_cases i <;> rfl

/-- Actual indexed honest projections supply leaves, for every candidate count and swap. -/
theorem honest_projection_product {n : Nat} (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (i : Fin 2) (j : Fin (n + 1)) :
    CiphertextProduct (frame ns swap left right).value (publicKey ns)
      ((Term.var i.succ : Recipe 3).project j.val)
      (.const (if j = choice swap left right i then .one else .zero)) (.name (ns.nonce i j)) := by
  apply honest_component_product ns swap left right _ i j
  change EqE (((Term.var i.succ : Recipe 3).project j.val).subst (frame ns swap left right).value) _
  rw [Term.subst_project]
  simp only [Term.subst, frame_voter_handle]
  exact ballot_project_ciphertext ns i (choice swap left right i) j

/-- The product case of normal-form composition retains its factor-origin certificate. -/
theorem minimum_product_decryption_normal_form {n : Nat} (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (a b p : Recipe 3) (nonce : Ground)
    (hc : CiphertextProduct (frame ns swap left right).value (publicKey ns) b p nonce)
    (hm : MinimalRecipe ns.nonceNames (frame ns swap left right).value (.binary .dec a b))
    {a' b' t : Ground} (ha : Irreducible a') (hb : Irreducible b') (ht : Irreducible t)
    (hea : EqE ((frame ns swap left right).eval a) a')
    (heb : EqE ((frame ns swap left right).eval b) b')
    (he : EqE ((frame ns swap left right).eval (.binary .dec a b)) t) :
    BaseEq t (.binary .dec a' b') :=
  hc.minimum_decryption_normal_form a hm ha hb ht hea heb he

end ExplainableCrypto.Helios.Symbolic.Historical
