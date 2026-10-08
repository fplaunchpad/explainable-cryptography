import ExplainableCrypto.Helios.Symbolic.StuckMinimumTools
import ExplainableCrypto.Helios.Symbolic.ExpandedSuccessfulProjections

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem handle_not_stuck_head (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (t : Ground)
    (ht : Irreducible t) (hk : t.StuckDestructorHead) (v : Fin (ExpandedHandles n)) :
    ¬ EqE ((expandedFrame ns swap left right rs).value v) t := by
  refine Fin.addCases (fun old => ?_) (fun extra => ?_) v
  · intro he
    have hv : EqE ((frame ns swap left right).value old) t := by
      simpa only [expandedFrame,Fin.addCases_left] using he
    fin_cases old
    · obtain ⟨_,rfl,_⟩ := hv.pk_irreducible_shape ht
      simp [Term.StuckDestructorHead,Term.headTag] at hk
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 0 0 (by unfold fieldCount; omega)
      obtain ⟨_,_,rfl,_⟩ := (hp.symm.trans hv).passive_binary_irreducible_shape (Or.inl rfl) ht
      simp [Term.StuckDestructorHead,Term.headTag] at hk
    · obtain ⟨a,b,hp⟩ := ballot_tail_pair_value ns swap left right 1 0 (by unfold fieldCount; omega)
      obtain ⟨_,_,rfl,_⟩ := (hp.symm.trans hv).passive_binary_irreducible_shape (Or.inl rfl) ht
      simp [Term.StuckDestructorHead,Term.headTag] at hk
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) extra
    · intro he
      have hv : EqE (tallyPartial ns swap left right rs j) t := by
        simpa only [expandedFrame,Fin.addCases_right,Fin.addCases_left] using he
      obtain ⟨_,_,rfl,_⟩ := hv.passive_binary_irreducible_shape (Or.inr rfl) ht
      simp [Term.StuckDestructorHead,Term.headTag] at hk
    · intro he
      obtain ⟨number,hnum⟩ := hn j
      have hv : EqE (addNumeral number) t := hnum.symm.trans
        (by simpa only [expandedFrame,Fin.addCases_right] using he)
      have hh := ((irreducible_eqE_iff_base (addNumeral_irreducible number) ht).mp hv).head_eq
      rcases hk with ⟨f,hf,hk⟩ | hk
      · rw [hk] at hh
        cases number <;> cases hh
      · rw [hk] at hh
        cases number <;> cases hh

private theorem minimum_normal_stuck_head (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {t : Ground} (ht : Irreducible t) (hk : t.StuckDestructorHead)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) t) :
    (r.subst (fun _ => (.const .bottom : Ground))).headTag = t.headTag :=
  (expandedFrame ns swap left right rs).minimum_normal_stuck_head_of_origins restricted
    (fun f hf a hm _ _ hp => (expanded_minimum_successful_projection_form ns swap left right rs hn restricted f hf a hm hp).data_value ns swap left right rs)
    (fun a b hm => expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm)
    (handle_not_stuck_head ns swap left right rs hn) r hm ht hk he

/-- Full-E stuck projection values force the exact selector and an argument
with no pair value. The target argument need not be normal. -/
theorem expanded_minimum_stuck_projection_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    (f : Unary) (hf : f = .fst ∨ f = .snd) {a : Ground}
    (hfail : ∀ x y, ¬ EqE a (.binary .pair x y))
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.unary f a)) :
    ∃ b, r = .unary f b ∧ ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).eval b) (.binary .pair x y) :=
  (expandedFrame ns swap left right rs).minimum_stuck_projection_form_of_head restricted
    (fun f hf a hm _ _ hp => (expanded_minimum_successful_projection_form ns swap left right rs hn restricted f hf a hm hp).data_value ns swap left right rs)
    (fun r hm _ ht hk he => minimum_normal_stuck_head ns swap left right rs hn restricted r hm ht hk he)
    r hm f hf hfail he

/-- Full-E stuck decryption values force ordered decryption syntax. Every
source minimum decryption is unmatched; no target normality is assumed. -/
theorem expanded_minimum_stuck_decryption_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {a b : Ground} (hfail : ∀ out, ¬ DecryptionMatch a b out)
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .dec a b)) :
    ∃ u v, r = .binary .dec u v ∧
      ∀ out, ¬ DecryptionMatch ((expandedFrame ns swap left right rs).eval u) ((expandedFrame ns swap left right rs).eval v) out :=
  (expandedFrame ns swap left right rs).minimum_stuck_decryption_form_of_head restricted
    (fun a b hm => expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm)
    (fun r hm _ ht hk he => minimum_normal_stuck_head ns swap left right rs hn restricted r hm ht hk he)
    r hm hfail he

/-- A stuck projection of a minimum child is minimum: every competitor has
the same selector and its argument must have at least the child's cost. -/
theorem expanded_minimum_stuck_projection_of_child (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (f : Unary) (hf : f = .fst ∨ f = .snd) (a : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hfail : ∀ x y, ¬ EqE ((expandedFrame ns swap left right rs).eval a) (.binary .pair x y)) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value (.unary f a) := by
  have hp : (Term.unary f a).Public restricted := ha.isPublic
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hp
  obtain ⟨b,rfl,hb⟩ := expanded_minimum_stuck_projection_form ns swap left right rs hn restricted m hm f hf hfail he.symm
  have harg := ((EqE.projection_iff_of_no_pair f f hf hf _ _ hfail hb).mp he).2
  have hsize := ha.least b hm.isPublic harg
  exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)

/-- A stuck decryption of minimum children is minimum. Successful E5/E6
expressions are explicitly outside this constructor-closure statement. -/
theorem expanded_minimum_stuck_decryption_of_children (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (a b : Recipe (ExpandedHandles n))
    (ha : MinimalRecipe restricted (expandedFrame ns swap left right rs).value a)
    (hb : MinimalRecipe restricted (expandedFrame ns swap left right rs).value b)
    (hfail : ∀ out, ¬ DecryptionMatch ((expandedFrame ns swap left right rs).eval a) ((expandedFrame ns swap left right rs).eval b) out) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value (.binary .dec a b) := by
  have hp : (Term.binary .dec a b).Public restricted := ⟨ha.isPublic,hb.isPublic⟩
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (expandedFrame ns swap left right rs).value) _ hp
  obtain ⟨u,v,rfl,hno⟩ := expanded_minimum_stuck_decryption_form ns swap left right rs hn restricted m hm hfail he.symm
  have hargs := (EqE.decryption_iff_of_no_match _ _ _ _ hfail hno).mp he
  have hu := ha.least u hm.isPublic.1 hargs.1
  have hv := hb.least v hm.isPublic.2 hargs.2
  exact hm.of_equivalent_size hp he (by simp only [Term.nodeCount]; omega)

end ExplainableCrypto.Helios.Symbolic.Historical.General
