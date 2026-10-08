import ExplainableCrypto.Helios.Symbolic.SourceOpeningDerivation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

theorem NameAssignment.FaithfulOn.update_fresh {ρ : NameAssignment} {S : Finset SourceName}
    (h : ρ.FaithfulOn S) (n : SourceName) (v : Nat)
    (hf : n.withValue v ∉ S.image (SourceName.map ρ.base ρ.channel)) :
    NameAssignment.FaithfulOn (Function.update ρ n v) S := by
  intro a b ha hb he
  by_cases han : a=n
  · subst a
    by_cases hbn : b=n
    · exact hbn.symm
    · rw [SourceName.map_update_self,SourceName.map_update_other n b _ v hbn] at he
      exact (hf (Finset.mem_image.mpr ⟨b,hb,he.symm⟩)).elim
  · by_cases hbn : b=n
    · subst b
      rw [SourceName.map_update_other n a _ v han,SourceName.map_update_self] at he
      exact (hf (Finset.mem_image.mpr ⟨a,ha,he⟩)).elim
    · rw [SourceName.map_update_other n a _ v han,SourceName.map_update_other n b _ v hbn] at he
      exact h ha hb he

theorem nameAssignment_fresh_update_image (ρ : NameAssignment) (S : Finset SourceName)
    (n : SourceName) (v : Nat) (m : SourceName)
    (hm : m ∉ S.image (SourceName.map ρ.base ρ.channel)) (hn : m ≠ n.withValue v) :
    m ∉ S.image (SourceName.map (NameAssignment.base (Function.update ρ n v))
      (NameAssignment.channel (Function.update ρ n v))) := by
  rintro h
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
  by_cases hxn : x=n
  · subst x
    rw [SourceName.map_update_self] at he
    exact hn he.symm
  · rw [SourceName.map_update_other n x _ v hxn] at he
    exact hm (Finset.mem_image.mpr ⟨x,hx,he⟩)

namespace Named
variable {V : Type}

/-- Opening a pure restriction bound supplies one actual assignment to its
whole Extended body. Fresh distinct allocations preserve finite faithfulness;
the theorem constructs the witness rather than adding it as a premise. -/
theorem Opens.prefix_faithful (bound : List SourceName) (a : Extended V)
    (ρ : NameAssignment) {ns : List SourceName} {b : Extended V}
    (h : Opens (restrictNames bound (.embed a)) ρ ns b) (S : Finset SourceName)
    (hi : ρ.FaithfulOn S)
    (hf : ∀ n ∈ ns, n ∉ S.image (SourceName.map ρ.base ρ.channel)) :
    ∃ τ : NameAssignment, b = a.mapNames τ.base τ.channel ∧ τ.FaithfulOn S ∧
      ∀ n, n ∉ bound → τ n = ρ n := by
  induction bound generalizing ρ ns with
  | nil =>
    cases h with
    | embed => exact ⟨ρ,rfl,hi,fun _ _ => rfl⟩
  | cons n bound ih =>
    cases h with
    | newName _ v h hn =>
      obtain ⟨τ,hb,ht,hfix⟩ := ih (Function.update ρ n v) h
        (hi.update_fresh n v (hf _ List.mem_cons_self))
        (fun m hm => nameAssignment_fresh_update_image ρ S n v m
          (hf m (List.mem_cons_of_mem _ hm)) (fun he => hn (he ▸ hm)))
      refine ⟨τ,hb,ht,?_⟩
      intro m hm
      have hmn : m ≠ n := fun he => hm (he ▸ List.mem_cons_self)
      rw [hfix m (fun hmem => hm (List.mem_cons_of_mem _ hmem)),Function.update_of_ne hmn]

theorem Opens.prefix_permutations (bound : List SourceName) (a : Extended V)
    {ns : List SourceName} {b : Extended V}
    (h : Opens (restrictNames bound (.embed a)) NameAssignment.literal ns b)
    (hf : ∀ n ∈ ns, n ∉ a.nameSupport) :
    ∃ e k : Nat ≃ Nat, b = a.mapNames e k := by
  have hmap : SourceName.map NameAssignment.literal.base NameAssignment.literal.channel = id := by
    funext n; cases n <;> rfl
  have hi : NameAssignment.literal.FaithfulOn a.nameSupport := by
    intro x y hx hy he
    simpa only [hmap,id_eq] using he
  have hf' : ∀ n ∈ ns, n ∉ a.nameSupport.image
      (SourceName.map NameAssignment.literal.base NameAssignment.literal.channel) := by
    simpa only [hmap,Finset.image_id] using hf
  obtain ⟨τ,hb,ht,_⟩ := h.prefix_faithful bound a NameAssignment.literal a.nameSupport hi hf'
  obtain ⟨e,k,he,hk⟩ := ht.exists_permutations
  exact ⟨e,k,hb.trans (a.mapAssignments_eq_permutations τ e k he hk)⟩

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
