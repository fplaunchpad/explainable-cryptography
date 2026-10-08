import ExplainableCrypto.Helios.Symbolic.ProjectionMinimumTransport

namespace ExplainableCrypto.Helios.Symbolic.Combination
variable {α : Type}

theorem indices_card_pos (a : Combination α) : 0 < a.indices.card := by
  induction a with
  | leaf => simp only [indices, Multiset.card_singleton]; omega
  | mul a b ha hb => simp only [indices, Multiset.card_add]; omega

/-- Multiplicity prevents any binary combination from being a singleton bag. -/
theorem eq_leaf_of_indices_singleton {a : Combination α} {i : α}
    (h : a.indices = {i}) : a = .leaf i := by
  cases a with
  | leaf j =>
    have hi := Multiset.singleton_inj.mp h
    exact congrArg Combination.leaf hi
  | mul a b =>
    have hc := congrArg Multiset.card h
    have := a.indices_card_pos
    have := b.indices_card_pos
    simp only [indices, Multiset.card_add, Multiset.card_singleton] at hc
    omega

end ExplainableCrypto.Helios.Symbolic.Combination

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Grouping cannot erase a constructed leaf or a second honest occurrence. -/
theorem CiphertextAssembly.eq_honest_of_singleton_group (t : CiphertextAssembly n) (i : HonestIndex n)
    (h : t.group = .honest (.leaf i)) : t = .honest i := by
  cases t with
  | constructed k r p => cases h
  | honest j =>
    change CiphertextGroup.honest (Combination.leaf j) = .honest (.leaf i) at h
    cases h
    rfl
  | mul a b =>
    simp only [CiphertextAssembly.group] at h
    cases ha : a.group <;> cases hb : b.group <;>
      simp only [ha,hb,CiphertextGroup.merge] at h <;> cases h

/-- A minimum public recipe equal to one fresh honest ciphertext is exactly its
indexed selector. Public and mixed groups are excluded by full-E nonce provenance. -/
theorem minimum_honest_ciphertext_origin (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (i : Fin 2) (j : Fin (n+1))
    (he : EqE ((frame ns swap left right).eval r) (ciphertext ns i (choice swap left right i).value j)) :
    r = (Term.var i.succ).project j.val := by
  obtain ⟨t,rfl,_,hpub,_,_,_,_,hnonce,hmessage⟩ :=
    minimum_ciphertext_grouping ns swap left right ns.restricted r hm he
  have hp := hpub.of_subset (show ns.nonceNames ⊆ ns.restricted from fun _ h => Finset.mem_union_right _ h)
  have obs := (CiphertextGroup.components_eq_iff ns hf swap left right t.group (.honest (.leaf (i,j)))
    hp trivial).mp ⟨hnonce,hmessage⟩
  cases hg : t.group with
  | constructed a b => simp only [hg,CiphertextGroup.Observation] at obs
  | mixed a b c => simp only [hg,CiphertextGroup.Observation] at obs
  | honest a =>
    have hi : a.indices = {(i,j)} := by simpa only [hg,CiphertextGroup.Observation,Combination.indices] using obs
    have ha := Combination.eq_leaf_of_indices_singleton hi
    have ht := t.eq_honest_of_singleton_group (i,j) (by rw [hg,ha])
    rw [ht]
    rfl

/-- Exact minimum size j+2 for every honest ciphertext selector, in either
assignment and with arbitrary valid E-equivalent candidate representatives. -/
theorem minimum_ciphertext_selector (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (i : Fin 2) (j : Fin (n+1)) :
    MinimalRecipe ns.restricted (frame ns swap left right).value ((Term.var i.succ).project j.val) := by
  have hp := (ProjectionChain.project i.succ j.val).isPublic ns.restricted
  have hv : EqE ((frame ns swap left right).eval ((Term.var i.succ).project j.val))
      (ciphertext ns i (choice swap left right i).value j) :=
    combination_value ns swap left right (.leaf (i,j))
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) _ hp
  have hs := minimum_honest_ciphertext_origin ns hf swap left right r hr i j (he.symm.trans hv)
  exact hs ▸ hr

end ExplainableCrypto.Helios.Symbolic.Historical.General
