import ExplainableCrypto.Helios.Symbolic.HistoricalFrameProtection
import Mathlib.Data.List.FinRange

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {V α : Type} {n : Nat}

private theorem fold_ciphertexts (xs : List α) (key : Term V) (rs ms : α → Term V)
    (c r m : Term V) (hc : EqE c (.ternary .penc key r m)) :
    EqE (xs.foldl (fun acc j => .binary .mul acc (.ternary .penc key (rs j) (ms j))) c)
      (.ternary .penc key (xs.foldl (fun acc j => .binary .compose acc (rs j)) r)
        (xs.foldl (fun acc j => .binary .add acc (ms j)) m)) := by
  induction xs generalizing c r m with
  | nil => exact hc
  | cons j xs ih =>
    exact ih _ _ _ ((EqE.binary .mul hc (.refl _)).trans
      (RootStep.homomorphic key r (rs j) m (ms j)).to_modulo.sound)

theorem foldCandidates_ciphertexts (key : Term V) (rs ms : Fin (n + 1) → Term V) :
    EqE (foldCandidates .mul (fun j => .ternary .penc key (rs j) (ms j)))
      (.ternary .penc key (foldCandidates .compose rs) (foldCandidates .add ms)) :=
  fold_ciphertexts (List.finRange n) key (fun j => rs j.succ) (fun j => ms j.succ) _ _ _ (.refl _)

private theorem fold_votes_summary (chosen : Fin (n + 1)) (xs : List (Fin (n + 1)))
    (a : Ground) (k : Nat) (ha : a.addSummary = .number k) :
    (xs.foldl (fun acc j => .binary .add acc (vote chosen j)) a).addSummary =
      .number (k + xs.count chosen) := by
  induction xs generalizing a k with
  | nil => simpa using ha
  | cons j xs ih =>
    have hb : (Term.binary .add a (vote chosen j)).addSummary =
        .number (k + if j = chosen then 1 else 0) := by
      by_cases h : j = chosen <;> simp [Term.addSummary, ha, vote, h]
    rw [List.foldl_cons, ih _ _ hb]
    by_cases h : j = chosen <;> simp [h, Nat.add_assoc, Nat.add_comm]

/-- Exact one-hot sum in E0; no global zero identity is used. -/
theorem vote_sum_one (chosen : Fin (n + 1)) :
    BaseEq (foldCandidates .add (vote chosen)) (.const .one) := by
  apply (baseEq_iff_addSummary _ _).mpr
  have h₀ : (vote chosen 0).addSummary = .number (if (0 : Fin (n + 1)) = chosen then 1 else 0) := by
    by_cases h : (0 : Fin (n + 1)) = chosen <;> simp [vote, h, Term.addSummary]
  have hs := fold_votes_summary chosen ((List.finRange n).map Fin.succ) _ _ h₀
  have hc := List.count_finRange chosen
  rw [List.finRange_succ, List.count_cons] at hc
  have hcount : (if (0 : Fin (n + 1)) = chosen then 1 else 0) +
      ((List.finRange n).map Fin.succ).count chosen = 1 := by
    by_cases h : (0 : Fin (n + 1)) = chosen <;> simpa [h, Nat.add_comm] using hc
  rw [hcount] at hs
  simpa only [foldCandidates, List.foldl_map, Term.addSummary] using hs

theorem ciphertext_product (ns : Names n) (i : Fin 2) (chosen : Fin (n + 1)) :
    EqE (foldCandidates .mul (ciphertext ns i chosen))
      (.ternary .penc (publicKey ns) (foldCandidates .compose (fun j => .name (ns.nonce i j))) (.const .one)) :=
  (foldCandidates_ciphertexts (publicKey ns) (fun j => .name (ns.nonce i j)) (vote chosen)).trans
    (.ternary .penc (.refl _) (.refl _) (vote_sum_one chosen).sound)

end ExplainableCrypto.Helios.Symbolic.Historical
