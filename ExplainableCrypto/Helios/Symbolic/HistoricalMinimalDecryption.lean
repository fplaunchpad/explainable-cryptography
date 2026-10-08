import ExplainableCrypto.Helios.Symbolic.MinimalDecryption
import ExplainableCrypto.Helios.Symbolic.HistoricalFrames

namespace ExplainableCrypto.Helios.Symbolic.Historical

/-- Honest component plaintexts are public constants. A minimum decrypt cannot
match them, even when its ciphertext argument is an arbitrary equivalent recipe.
The name policy is exactly the nonce-only policy used in Lemma 9. -/
theorem minimum_honest_component_no_decryption_match {n : Nat} (ns : Names n)
    (swap : Bool) (left right : Fin (n + 1)) (a b : Recipe 3)
    (h : MinimalRecipe ns.nonceNames (frame ns swap left right).value (.binary .dec a b))
    (i : Fin 2) (j : Fin (n + 1))
    (hb : EqE ((frame ns swap left right).eval b)
      (ciphertext ns i (choice swap left right i) j)) (m : Ground) :
    ¬ DecryptionMatch ((frame ns swap left right).eval a)
      ((frame ns swap left right).eval b) m :=
  h.constant_plaintext_no_decryption_match a b (publicKey ns) (.name (ns.nonce i j))
    (if j = choice swap left right i then .one else .zero) hb m

/-- This covers every right-argument recipe E-equal to an actual honest component,
not only the literal field projection. Target normality and minimum size are explicit. -/
theorem minimum_honest_component_decryption_normal_shape {n : Nat} (ns : Names n)
    (swap : Bool) (left right : Fin (n + 1)) (a b : Recipe 3)
    (h : MinimalRecipe ns.nonceNames (frame ns swap left right).value (.binary .dec a b))
    (i : Fin 2) (j : Fin (n + 1))
    (hb : EqE ((frame ns swap left right).eval b)
      (ciphertext ns i (choice swap left right i) j))
    {t : Ground} (ht : Irreducible t)
    (he : EqE ((frame ns swap left right).eval (.binary .dec a b)) t) :
    ∃ a' b', t = .binary .dec a' b' ∧
      EqE ((frame ns swap left right).eval a) a' ∧ EqE ((frame ns swap left right).eval b) b' :=
  decryption_normal_shape_of_no_match _ _
    (minimum_honest_component_no_decryption_match ns swap left right a b h i j hb) ht he

/-- Exact normal-form composition modulo E0 for the honest-component value case. -/
theorem minimum_honest_component_decryption_normal_form {n : Nat} (ns : Names n)
    (swap : Bool) (left right : Fin (n + 1)) (a b : Recipe 3)
    (h : MinimalRecipe ns.nonceNames (frame ns swap left right).value (.binary .dec a b))
    (i : Fin 2) (j : Fin (n + 1))
    (hc : EqE ((frame ns swap left right).eval b)
      (ciphertext ns i (choice swap left right i) j))
    {a' b' t : Ground} (ha : Irreducible a') (hb : Irreducible b') (ht : Irreducible t)
    (hea : EqE ((frame ns swap left right).eval a) a')
    (heb : EqE ((frame ns swap left right).eval b) b')
    (he : EqE ((frame ns swap left right).eval (.binary .dec a b)) t) :
    BaseEq t (.binary .dec a' b') :=
  decryption_normal_form_of_no_match _ _
    (minimum_honest_component_no_decryption_match ns swap left right a b h i j hc)
    ha hb ht hea heb he

end ExplainableCrypto.Helios.Symbolic.Historical
