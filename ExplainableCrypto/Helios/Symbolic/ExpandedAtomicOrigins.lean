import ExplainableCrypto.Helios.Symbolic.ExpandedProjectionOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Old key/ballot handles and new partial handles cannot have atomic values.
Only result slots remain; this classification does not assume numeric results. -/
theorem expanded_handle_atomic_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (v : Fin (ExpandedHandles n))
    (t : Ground) (ht : t.nodeCount = 1)
    (he : EqE ((expandedFrame ns swap left right rs).value v) t) :
    ∃ j : Fin (n+1), v = expandedResult j := by
  revert he
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro he
    exact False.elim (frame_handle_not_atom ns swap left right old t ht
      (by simpa only [expandedFrame,Fin.addCases_left] using he))
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro he
      have hval : EqE (tallyPartial ns swap left right rs j) t := by
        simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left] using he
      obtain ⟨a,b,hs,_⟩ := hval.passive_binary_irreducible_shape (Or.inr rfl) (ground_atom_irreducible ht)
      have hsize := congrArg Term.nodeCount hs
      have ha := a.nodeCount_pos
      have hb := b.nodeCount_pos
      simp only [Term.nodeCount] at hsize
      omega
    · intro _
      exact ⟨j,rfl⟩

private theorem numeral_not_name (number name : Nat) : ¬ EqE (addNumeral (V := Empty) number) (.name name) := by
  intro he
  have hh := ((irreducible_eqE_iff_base (addNumeral_irreducible number) (name_irreducible name)).mp he).head_eq
  cases number <;> cases hh

theorem expanded_handle_not_name (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (v : Fin (ExpandedHandles n)) (name : Nat) :
    ¬ EqE ((expandedFrame ns swap left right rs).value v) (.name name) := by
  intro he
  obtain ⟨j,rfl⟩ := expanded_handle_atomic_origin ns swap left right rs v (.name name) rfl he
  obtain ⟨number,hnum⟩ := hn j
  exact numeral_not_name number name (hnum.symm.trans (by simpa only [expanded_frame_result] using he))

/-- Exact deducibility under the actual full name policy survives publication. -/
theorem expanded_name_deducible_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (name : Nat) :
    (∃ r : Recipe (ExpandedHandles n), r.Public ns.restricted ∧
      EqE ((expandedFrame ns swap left right rs).eval r) (.name name)) ↔ name ∉ ns.restricted := by
  constructor
  · rintro ⟨r,hr,he⟩ hn
    exact (expanded_frame_opaque_protected ns swap left right rs hp).name_not_deducible r hr hn he
  · intro hn
    exact ⟨.name name,hn,.refl _⟩

theorem expanded_minimum_name_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (hn : ExpandedResultsNumeric ns swap left right rs)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r)
    (name : Nat) (he : EqE ((expandedFrame ns swap left right rs).eval r) (.name name)) : r = .name name := by
  have hpublic := (expanded_name_deducible_iff ns swap left right rs hp name).mp ⟨r,hm.isPublic,he⟩
  have hsize := hm.least (.name name) hpublic he
  rcases Term.nodeCount_one_cases hsize with ⟨x,rfl⟩ | ⟨v,rfl⟩ | ⟨c,rfl⟩
  · exact congrArg Term.name ((EqE.name_iff _ _).mp he)
  · exact False.elim (expanded_handle_not_name ns swap left right rs hn v name he)
  · exact False.elim (name_not_eqE_const name c he.symm)

/-- Constant minima include published result handles. Their target value is
retained explicitly; the old literal-only atomic lemma does not extend. -/
theorem expanded_minimum_constant_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    (c : Constant) (he : EqE ((expandedFrame ns swap left right rs).eval r) (.const c)) :
    r = .const c ∨ ∃ j : Fin (n+1), r = .var (expandedResult j) ∧ EqE (tallyResult ns swap left right rs j) (.const c) := by
  have hsize := hm.least (.const c) trivial he
  rcases Term.nodeCount_one_cases hsize with ⟨x,rfl⟩ | ⟨v,rfl⟩ | ⟨d,rfl⟩
  · exact False.elim (name_not_eqE_const x c he)
  · obtain ⟨j,rfl⟩ := expanded_handle_atomic_origin ns swap left right rs v (.const c) rfl he
    exact Or.inr ⟨j,rfl,by simpa only [Frame.eval,Term.subst,expanded_frame_result] using he⟩
  · exact Or.inl (congrArg Term.const ((EqE.const_iff _ _).mp he))

end ExplainableCrypto.Helios.Symbolic.Historical.General
