import ExplainableCrypto.Helios.Symbolic.SourceNameOpening

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

theorem SourceName.map_assignment_eq (n : SourceName) (ρ : NameAssignment) :
    n.map ρ.base ρ.channel = n.withValue (ρ n) := by cases n <;> rfl

theorem SourceName.map_update_self (n : SourceName) (ρ : NameAssignment) (v : Nat) :
    n.map (NameAssignment.base (Function.update ρ n v)) (NameAssignment.channel (Function.update ρ n v)) = n.withValue v := by
  rw [SourceName.map_assignment_eq,Function.update_self]

theorem SourceName.map_update_other (n m : SourceName) (ρ : NameAssignment) (v : Nat) (h : m ≠ n) :
    m.map (NameAssignment.base (Function.update ρ n v)) (NameAssignment.channel (Function.update ρ n v)) = m.map ρ.base ρ.channel := by
  rw [SourceName.map_assignment_eq,Function.update_of_ne h,SourceName.map_assignment_eq]

namespace Named
variable {V : Type}

/-- Every output name is either the image of a genuinely free source name or
one of the explicitly allocated binders. Complete payload/guard fields count. -/
theorem Opens.nameSupport {a : Named V} {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended V} (h : Opens a ρ ns b) :
    b.nameSupport ⊆ a.freeNames.image (SourceName.map ρ.base ρ.channel) ∪ ns.toFinset := by
  induction h with
  | embed a ρ => simp only [Extended.nameSupport_mapNames,freeNames,List.toFinset_nil,Finset.union_empty,Finset.Subset.refl]
  | par ha hb hd ih ij =>
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · rcases Finset.mem_union.mp (ih hn) with hn | hn
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr (by
          obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
          exact ⟨m,Finset.mem_union_left _ hm,he⟩))
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hn)))
    · rcases Finset.mem_union.mp (ij hn) with hn | hn
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr (by
          obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
          exact ⟨m,Finset.mem_union_right _ hm,he⟩))
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hn)))
  | newName n v ha hf ih =>
    intro m hm
    rcases Finset.mem_union.mp (ih hm) with hm | hm
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
      by_cases he : x=n
      · subst x
        rw [SourceName.map_update_self]
        exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_cons_self))
      · rw [SourceName.map_update_other n x _ v he]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,Finset.mem_erase.mpr ⟨he,hx⟩,rfl⟩)
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp hm)))
  | newVar ha ih => exact ih

theorem Opens.fresh_for_opened_context {a : Named V} {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended V} (h : Opens a ρ ns b) (m : SourceName)
    (hf : m ∉ a.freeNames.image (SourceName.map ρ.base ρ.channel)) (hn : m ∉ ns) :
    m ∉ b.nameSupport := by
  intro hm
  rcases Finset.mem_union.mp (h.nameSupport hm) with hm | hm
  · exact hf hm
  · exact hn (List.mem_toFinset.mp hm)

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
