import ExplainableCrypto.Helios.Symbolic.HistoricalAcceptedProofs

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Full E gives a raw factor-count upper bound only against an irreducible target. -/
theorem EqE.compose_card_le_of_irreducible {a b : Term V} (he : EqE a b)
    (hb : Irreducible b) : a.composeFactors.card ≤ b.composeFactors.card := by
  obtain ⟨w, ha, hw⟩ := (eqE_iff_join _ _).mp he
  have hbase := hb.reducesModulo hw
  simpa only [← hbase.compose_factors] using ha.compose_card_le

theorem Term.Public.drop {restricted : Finset Nat} {t : Term V}
    (h : t.Public restricted) (i : Nat) : (t.drop i).Public restricted := by
  induction i generalizing t with
  | zero => exact h
  | succ i ih => exact ih h

theorem Term.Public.project {restricted : Finset Nat} {t : Term V}
    (h : t.Public restricted) (i : Nat) : (t.project i).Public restricted := h.drop i

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {V α : Type} {n : Nat}

private theorem foldl_congr (xs : List α) (f : Binary) (rs ss : α → Term V)
    (a b : Term V) (hab : EqE a b) (h : ∀ j, EqE (rs j) (ss j)) :
    EqE (xs.foldl (fun acc j => .binary f acc (rs j)) a)
      (xs.foldl (fun acc j => .binary f acc (ss j)) b) := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons j xs ih => exact ih _ _ (.binary f hab (h j))

theorem foldCandidates_congr (f : Binary) (rs ss : Fin (n + 1) → Term V)
    (h : ∀ j, EqE (rs j) (ss j)) : EqE (foldCandidates f rs) (foldCandidates f ss) :=
  foldl_congr _ f _ _ _ _ (h 0) (fun j => h j.succ)

private theorem foldl_factors (xs : List α) (rs : α → Term V) (a : Term V) :
    (xs.foldl (fun acc j => .binary .compose acc (rs j)) a).composeFactors =
      a.composeFactors + (xs.map (fun j => (rs j).composeFactors)).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons j xs ih => simp only [List.foldl_cons, ih, Term.composeFactors, List.map_cons,
      List.sum_cons, add_assoc]

/-- Exact multiplicities, with no composition unit in the term language. -/
theorem foldCandidates_compose_factors (rs : Fin (n + 1) → Term V) :
    (foldCandidates .compose rs).composeFactors =
      ((List.finRange (n + 1)).map (fun j => (rs j).composeFactors)).sum := by
  simp only [foldCandidates, foldl_factors, List.finRange_succ, List.map_cons,
    List.map_map, List.sum_cons, Function.comp_def]

private theorem mem_sum (xs : List α) (rs : α → Multiset (BaseClass V)) (q : BaseClass V) :
    q ∈ (xs.map rs).sum ↔ ∃ j ∈ xs, q ∈ rs j := by
  induction xs with
  | nil => simp
  | cons j xs ih => simp [ih]

theorem mem_foldCandidates_compose (rs : Fin (n + 1) → Term V) (q : BaseClass V) :
    q ∈ (foldCandidates .compose rs).composeFactors ↔ ∃ j, q ∈ (rs j).composeFactors := by
  rw [foldCandidates_compose_factors, mem_sum]
  simp

private theorem foldl_card (xs : List α) (rs : α → Term V) (a : Term V) :
    (xs.foldl (fun acc j => .binary .compose acc (rs j)) a).composeFactors.card =
      a.composeFactors.card + (xs.map (fun j => (rs j).composeFactors.card)).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons j xs ih => simp only [List.foldl_cons, ih, Term.composeFactors, Multiset.card_add,
      List.map_cons, List.sum_cons, Nat.add_assoc]

theorem foldCandidates_compose_card (rs : Fin (n + 1) → Term V) :
    (foldCandidates .compose rs).composeFactors.card =
      ((List.finRange (n + 1)).map (fun j => (rs j).composeFactors.card)).sum := by
  simp only [foldCandidates, foldl_card, List.finRange_succ, List.map_cons,
    List.map_map, List.sum_cons, Function.comp_def]

private theorem sum_positive (xs : List α) (f : α → Nat) (h : ∀ j, 0 < f j) :
    xs.length ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons j xs ih =>
    have hj := h j
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem sum_selected (xs : List α) (f : α → Nat) (h : ∀ j, 0 < f j)
    (j : α) (hj : j ∈ xs) : xs.length - 1 + f j ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hj
  | cons k xs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hj with rfl | hj
    · have hs := sum_positive xs f h
      omega
    · have hs := ih hj
      have hk := h k
      have hl := List.length_pos_of_mem hj
      omega

/-- One selected component contributes its whole bag; every other input adds at least one. -/
theorem foldCandidates_compose_selected_lower (rs : Fin (n + 1) → Term V) (j : Fin (n + 1)) :
    n + (rs j).composeFactors.card ≤ (foldCandidates .compose rs).composeFactors.card := by
  rw [foldCandidates_compose_card]
  have h := sum_selected (List.finRange (n + 1)) (fun j => (rs j).composeFactors.card)
    (fun j => Multiset.card_pos.mpr (rs j).composeFactors_nonempty) j (by simp)
  simpa using h

theorem named_nonce_fold_card (names : Fin (n + 1) → Nat) :
    (foldCandidates .compose (fun j => (Term.name (names j) : Term V))).composeFactors.card = n + 1 := by
  rw [foldCandidates_compose_card]
  simp [Term.composeFactors]

theorem named_nonce_fold_irreducible (names : Fin (n + 1) → Nat) :
    Irreducible (foldCandidates .compose (fun j => (Term.name (names j) : Term V))) := by
  apply irreducible_of_compose_factors
  intro a _ ha
  obtain ⟨j, hj⟩ := (mem_foldCandidates_compose _ _).mp ha
  have he : a.baseClass = (Term.name (V := V) (names j)).baseClass := by simpa [Term.composeFactors] using hj
  exact (name_irreducible (names j)).base ((baseClass_eq_iff _ _).mp he).symm

/-- Replace a component by an E-equal value without choosing normal forms for the others. -/
theorem foldCandidates_replace (rs : Fin (n + 1) → Term V) (j : Fin (n + 1)) (r : Term V)
    (he : EqE (rs j) r) :
    EqE (foldCandidates .compose rs)
      (foldCandidates .compose (fun k => if k = j then r else rs k)) := by
  apply foldCandidates_congr
  intro k
  by_cases hk : k = j
  · subst k
    simpa using he
  · simp only [hk, ↓reduceIte]
    exact .refl _

/-- The complete honest nonce aggregate cannot fit inside a same-sized normal
aggregate after adding the other nonempty component nonces. -/
theorem nonce_fold_not_eq_small_normal (hn : 0 < n) (rs : Fin (n + 1) → Term V)
    (j : Fin (n + 1)) (names : Fin (n + 1) → Nat)
    (hj : EqE (rs j) (foldCandidates .compose (fun k => .name (names k))))
    (target : Term V) (ht : Irreducible target) (hcard : target.composeFactors.card ≤ n + 1) :
    ¬ EqE (foldCandidates .compose rs) target := by
  intro he
  have hrepl := foldCandidates_replace rs j _ hj
  have hc := (hrepl.symm.trans he).compose_card_le_of_irreducible ht
  have hl := foldCandidates_compose_selected_lower
    (fun k => if k = j then (foldCandidates .compose (fun k => Term.name (names k))) else rs k) j
  simp only [↓reduceIte, named_nonce_fold_card] at hl
  omega

end ExplainableCrypto.Helios.Symbolic.Historical

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {n : Nat}

/-- If one component is an honest aggregate nonce, its name factors persist in
the whole composition, which cannot be supplied by a nonce-public recipe. -/
theorem frame_nonce_fold_not_deducible (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (recipe : Recipe 3) (hp : recipe.Public ns.nonceNames)
    (rs : Fin (n + 1) → Ground) (j : Fin (n + 1)) (i : Fin 2)
    (hj : EqE (rs j) (foldCandidates .compose (fun k => .name (ns.nonce i k)))) :
    ¬ EqE ((frame ns swap left right).eval recipe) (foldCandidates .compose rs) := by
  intro he
  have hrepl := foldCandidates_replace rs j _ hj
  have hmem : (Term.name (V := Empty) (ns.nonce i 0)).baseClass ∈
      (foldCandidates .compose (fun k =>
        if k = j then foldCandidates .compose (fun k => Term.name (ns.nonce i k)) else rs k)).composeFactors := by
    apply (mem_foldCandidates_compose _ _).mpr
    refine ⟨j, ?_⟩
    simp only [↓reduceIte]
    apply (mem_foldCandidates_compose _ _).mpr
    exact ⟨0, by simp [Term.composeFactors]⟩
  exact nonce_safe_not_eqE_name_factor
    (recipe.nonce_safe_subst (frame ns swap left right).value (hp.nonce_safe recipe)
      (frame_protected ns swap left right)) (ns.nonce_mem_nonceNames i 0) hmem
    (he.trans hrepl)

end ExplainableCrypto.Helios.Symbolic.Historical
