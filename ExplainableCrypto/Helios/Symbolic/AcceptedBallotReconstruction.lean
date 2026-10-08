import ExplainableCrypto.Helios.Symbolic.HistoricalAggregateExclusion
import ExplainableCrypto.Helios.Symbolic.BallotTupleValues

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {n : Nat}

/-- Substitution acts pointwise on the fixed tuple encoding. -/
theorem Term.subst_tuple (σ : V → Term W) (xs : List (Term V)) :
    (Term.tuple xs).subst σ = Term.tuple (xs.map (fun t => t.subst σ)) := by
  induction xs <;> simp_all [Term.tuple, Term.subst]

theorem Term.Public.tuple {restricted : Finset Nat} (xs : List (Term V))
    (h : ∀ t ∈ xs, t.Public restricted) : (Term.tuple xs).Public restricted := by
  induction xs with
  | nil => trivial
  | cons a xs ih => exact ⟨h a (by simp), ih (fun t ht => h t (by simp [ht]))⟩

/-- Reconstruction with independently supplied field values. -/
theorem tuple_value_from_fields (fields : List (Term V)) (t : Term V)
    (hp : ∀ i < fields.length, ∃ a b, EqE (t.drop i) (.binary .pair a b))
    (ht : EqE (t.drop fields.length) (.const .bottom))
    (hv : ∀ i (hi : i < fields.length), EqE (t.project i) fields[i]) :
    EqE t (Term.tuple fields) := by
  induction fields generalizing t with
  | nil => exact ht
  | cons a xs ih =>
    obtain ⟨x, y, hpair⟩ := hp 0 (by simp)
    have hrest := ih (.unary .snd t) (fun i hi => hp (i + 1) (by simpa using hi)) ht
      (fun i hi => hv (i + 1) (by simpa using hi))
    exact (pair_reconstruction_of_value hpair).trans
      (.binary .pair (hv 0 (by simp)) hrest)

/-- The explicit tuple shape required by Lemma 9, with one extra aggregate proof. -/
def constructorFields (key : Term V) (nonces messages : Fin (n + 1) → Term V)
    (proofs : Fin (n + 2) → Term V) : List (Term V) :=
  (List.finRange (n + 1)).map (fun j => .ternary .penc key (nonces j) (messages j)) ++
    (List.finRange (n + 2)).map proofs

def constructorBallot (key : Term V) (nonces messages : Fin (n + 1) → Term V)
    (proofs : Fin (n + 2) → Term V) : Term V :=
  Term.tuple (constructorFields key nonces messages proofs)

theorem constructorFields_length (key : Term V) (nonces messages : Fin (n + 1) → Term V)
    (proofs : Fin (n + 2) → Term V) :
    (constructorFields key nonces messages proofs).length = fieldCount n := by
  simp [constructorFields, fieldCount]
  omega

theorem constructorFields_ciphertext (key : Term V) (nonces messages : Fin (n + 1) → Term V)
    (proofs : Fin (n + 2) → Term V) (j : Fin (n + 1)) :
    (constructorFields key nonces messages proofs)[j.val]'(by rw [constructorFields_length]; unfold fieldCount; omega) =
      .ternary .penc key (nonces j) (messages j) := by
  simp [constructorFields, j.isLt]

theorem constructorFields_proof (key : Term V) (nonces messages : Fin (n + 1) → Term V)
    (proofs : Fin (n + 2) → Term V) (j : Fin (n + 2)) :
    (constructorFields key nonces messages proofs)[n + 1 + j.val]'(by rw [constructorFields_length]; unfold fieldCount; omega) =
      proofs j := by
  simp [constructorFields]

theorem constructorBallot_project_ciphertext (key : Term V) (nonces messages : Fin (n + 1) → Term V)
    (proofs : Fin (n + 2) → Term V) (j : Fin (n + 1)) :
    EqE ((constructorBallot key nonces messages proofs).project j.val)
      (.ternary .penc key (nonces j) (messages j)) := by
  have h := project_tuple_get (constructorFields key nonces messages proofs) j.val
    (by rw [constructorFields_length]; unfold fieldCount; omega)
  rw [constructorFields_ciphertext] at h
  exact h

theorem constructorBallot_public {restricted : Finset Nat} (key : Term V)
    (nonces messages : Fin (n + 1) → Term V) (proofs : Fin (n + 2) → Term V)
    (hk : key.Public restricted) (hr : ∀ j, (nonces j).Public restricted)
    (hm : ∀ j, (messages j).Public restricted) (hp : ∀ j, (proofs j).Public restricted) :
    (constructorBallot key nonces messages proofs).Public restricted := by
  apply Term.Public.tuple
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    exact ⟨hk, hr j, hm j⟩
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
    exact hp j

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical
variable {V W α : Type} {n : Nat}

private theorem subst_foldl (σ : V → Term W) (xs : List α) (f : Binary)
    (rs : α → Term V) (a : Term V) :
    (xs.foldl (fun acc j => .binary f acc (rs j)) a).subst σ =
      xs.foldl (fun acc j => .binary f acc ((rs j).subst σ)) (a.subst σ) := by
  induction xs generalizing a with
  | nil => rfl
  | cons j xs ih => simpa only [List.foldl_cons, Term.subst] using ih (.binary f a (rs j))

theorem foldCandidates_subst (σ : V → Term W) (f : Binary) (rs : Fin (n + 1) → Term V) :
    (foldCandidates f rs).subst σ = foldCandidates f (fun j => (rs j).subst σ) :=
  subst_foldl σ _ f _ _

/-- A constant-bit candidate condition also holds before historical substitution. -/
theorem candidate_bits_change_variables (bits : Fin (n + 1) → Constant)
    (h : CandidateValues (V := V) (fun j => .const (bits j))) :
    CandidateValues (V := W) (fun j => .const (bits j)) := by
  rcases h with h | h
  · have he := h.subst (fun _ => (Term.const .zero : Term W))
    exact Or.inl (by simpa only [foldCandidates_subst, Term.subst] using he)
  · have he := h.subst (fun _ => (Term.const .zero : Term W))
    exact Or.inr (by simpa only [foldCandidates_subst, Term.subst] using he)

/-- Lemma 9 reconstruction for the encoded one-hot historical frame and tail correction.
The explicit public witness may depend on the supplied swapped world. -/
theorem accepted_ballot_constructor_recipe (ns : Names n) (swap : Bool)
    (left right : Fin (n + 1)) (recipe : Recipe 3) (hp : recipe.Public ns.nonceNames)
    (board : List Ground) (ha : Accepted n (publicKey ns) board ((frame ns swap left right).eval recipe))
    (hboard : ∀ i : Fin 2, ballot ns i (choice swap left right i) ∈ board) :
    ∃ (nonces : Fin (n + 1) → Recipe 3) (bits : Fin (n + 1) → Constant)
      (proofs : Fin (n + 2) → Recipe 3),
      (∀ j, bits j = .zero ∨ bits j = .one) ∧
      CandidateValues (V := Fin 3) (fun j => .const (bits j)) ∧
      (∀ j, (nonces j).Public ns.nonceNames) ∧
      (∀ j, (proofs j).Public ns.nonceNames) ∧
      (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs).Public ns.nonceNames ∧
      EqE ((frame ns swap left right).eval recipe)
        ((frame ns swap left right).eval (constructorBallot (.var 0) nonces (fun j => .const (bits j)) proofs)) := by
  obtain ⟨v⟩ := (proofValid_iff_values _ _).mp ha.1
  choose nonces hnonces he using accepted_component_public_nonce ns swap left right recipe hp board ha hboard v
  let proofs := fun j : Fin (n + 2) => recipe.project (n + 1 + j.val)
  have hproofs : ∀ j, (proofs j).Public ns.nonceNames := fun j => hp.project _
  refine ⟨nonces, v.bit, proofs, v.isBit, candidate_bits_change_variables v.bit v.candidate,
    hnonces, hproofs, constructorBallot_public _ _ _ _ trivial hnonces (fun _ => trivial) hproofs, ?_⟩
  let fields := constructorFields (Term.var 0) nonces (fun j => .const (v.bit j)) proofs
  change EqE _ ((Term.tuple fields).subst (frame ns swap left right).value)
  rw [Term.subst_tuple]
  have hlen : (fields.map (fun t => t.subst (frame ns swap left right).value)).length = fieldCount n := by
    simp only [List.length_map, fields, constructorFields_length]
  apply tuple_value_from_fields
  · intro i hi
    exact ha.1.pair_tails i (hlen ▸ hi)
  · simpa only [hlen, TailGuard] using ha.2.1
  · intro index hi
    have hidx : index < fieldCount n := hlen ▸ hi
    simp only [List.getElem_map]
    by_cases hc : index < n + 1
    · have hf := constructorFields_ciphertext (Term.var 0) nonces (fun j => .const (v.bit j)) proofs ⟨index, hc⟩
      change EqE _ (((constructorFields (Term.var 0) nonces (fun j => .const (v.bit j)) proofs)[index]'(by rw [constructorFields_length]; exact hidx)).subst _)
      rw [hf]
      exact (v.ciphertext ⟨index, hc⟩).trans
        (.ternary .penc (.refl _) (he ⟨index, hc⟩).symm (.refl _))
    · have hj : index - (n + 1) < n + 2 := by unfold fieldCount at hidx; omega
      have hid : n + 1 + (index - (n + 1)) = index := by omega
      have hf := constructorFields_proof (Term.var 0) nonces (fun j => .const (v.bit j)) proofs ⟨index - (n + 1), hj⟩
      simp only [hid] at hf
      change EqE _ (((constructorFields (Term.var 0) nonces (fun j => .const (v.bit j)) proofs)[index]'(by rw [constructorFields_length]; exact hidx)).subst _)
      rw [hf]
      simp only [proofs, hid, Term.subst_project]
      exact .refl _

end ExplainableCrypto.Helios.Symbolic.Historical
