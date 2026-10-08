import ExplainableCrypto.Helios.Symbolic.BallotValues
import ExplainableCrypto.Helios.Symbolic.TupleProjectionPaths

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {n : Nat}

/-- In-range fields do not depend on the unchecked terminal tail. -/
theorem project_tupleWithTail_get (xs : List (Term V)) (tail : Term V)
    (i : Nat) (hi : i < xs.length) :
    EqE ((tupleWithTail xs tail).project i) xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => exact .equation (.fst a (tupleWithTail xs tail))
    | succ i =>
      exact (EqE.unary .fst ((EqE.equation (.snd a (tupleWithTail xs tail))).drop i)).trans
        (ih i (by simpa using hi))

/-- Pair reconstruction requires an actual pair value; E has no global pair eta. -/
theorem pair_reconstruction_of_value {t a b : Term V} (h : EqE t (.binary .pair a b)) :
    EqE t (.binary .pair (.unary .fst t) (.unary .snd t)) := by
  have hl := (EqE.unary .fst h).trans (.equation (.fst a b))
  have hr := (EqE.unary .snd h).trans (.equation (.snd a b))
  exact h.trans (.binary .pair hl.symm hr.symm)

/-- Reconstruct exactly the checked prefix, with its explicit terminal guard. -/
theorem tuple_reconstruction_of_pair_tails (count : Nat) (t : Term V)
    (hp : ∀ i < count, ∃ a b, EqE (t.drop i) (.binary .pair a b))
    (ht : EqE (t.drop count) (.const .bottom)) :
    EqE t (Term.tuple ((List.range count).map (fun i => t.project i))) := by
  induction count generalizing t with
  | zero => exact ht
  | succ count ih =>
    obtain ⟨a, b, he⟩ := hp 0 (by omega)
    have hs := ih (.unary .snd t) (fun i hi => hp (i + 1) (by omega)) ht
    have hout := (pair_reconstruction_of_value he).trans
      (.binary .pair (.refl _) hs)
    simpa only [List.range_succ_eq_map, List.map_cons, List.map_map,
      Term.tuple, Function.comp_def, Term.project, Term.drop] using hout

/-- Every field check forces its containing tail to have a pair value. -/
theorem ProofValid.pair_tails {key ballot : Term V} (h : ProofValid n key ballot)
    (i : Nat) (hi : i < fieldCount n) :
    ∃ a b, EqE (ballot.drop i) (.binary .pair a b) := by
  by_cases hc : i < n + 1
  · obtain ⟨_, _, _, he, _⟩ := (EqE.check_ok_iff_components _ _ _).mp (h.2 ⟨i, hc⟩)
    obtain ⟨a, b, hab, _⟩ := he.projection_penc_inversion (Or.inl rfl)
    exact ⟨a, b, hab.sound⟩
  · by_cases hp : i < 2 * (n + 1)
    · have hj : i - (n + 1) < n + 1 := by omega
      obtain ⟨_, _, _, _, he⟩ := (EqE.check_ok_iff_components _ _ _).mp (h.2 ⟨i - (n + 1), hj⟩)
      have hidx : n + 1 + (i - (n + 1)) = i := by omega
      simp only [hidx] at he
      obtain ⟨a, b, hab, _⟩ := he.projection_spk_inversion (Or.inl rfl)
      exact ⟨a, b, hab.sound⟩
    · have hidx : i = 2 * (n + 1) := by unfold fieldCount at hi; omega
      subst i
      obtain ⟨_, _, _, _, he⟩ := (EqE.check_ok_iff_components _ _ _).mp h.1
      obtain ⟨a, b, hab, _⟩ := he.projection_spk_inversion (Or.inl rfl)
      exact ⟨a, b, hab.sound⟩

/-- Validity plus the corrected guard implies finite tuple shape under full E. -/
theorem ProofValid.tuple_value {key ballot : Term V} (h : ProofValid n key ballot)
    (ht : TailGuard n ballot) :
    EqE ballot (Term.tuple ((List.range (fieldCount n)).map (fun i => ballot.project i))) :=
  tuple_reconstruction_of_pair_tails _ ballot h.pair_tails ht

end ExplainableCrypto.Helios.Symbolic
