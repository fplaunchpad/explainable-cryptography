import ExplainableCrypto.Helios.Symbolic.SourcePairedOpeningReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- A chosen source opening also opens a second body beneath the same name
prefix, using permutations that agree on the union of both endpoint supports.
The target opening retains the actual restrictions and the allocation list. -/
theorem Opens.prefix_permutations_pair (bound : List SourceName) (a c : Extended V)
    {ns : List SourceName} {b : Extended V}
    (h : Opens (restrictNames bound (.embed a)) NameAssignment.literal ns b)
    (hf : ∀ n ∈ ns, n ∉ a.nameSupport ∪ c.nameSupport) :
    ∃ e k : Nat ≃ Nat, b = a.mapNames e k ∧
      Opens (restrictNames bound (.embed c)) NameAssignment.literal ns (c.mapNames e k) := by
  have hmap : SourceName.map NameAssignment.literal.base NameAssignment.literal.channel = id := by
    funext n; cases n <;> rfl
  have hi : NameAssignment.literal.FaithfulOn (a.nameSupport ∪ c.nameSupport) := by
    intro x y hx hy he
    simpa only [hmap,id_eq] using he
  have hf' : ∀ n ∈ ns, n ∉ (a.nameSupport ∪ c.nameSupport).image
      (SourceName.map NameAssignment.literal.base NameAssignment.literal.channel) := by
    simpa only [hmap,Finset.image_id] using hf
  obtain ⟨τ,hb,ht,hc⟩ := h.prefix_faithful_pair bound a c NameAssignment.literal _ hi hf'
  obtain ⟨e,k,he,hk⟩ := ht.exists_permutations
  have ha' := a.mapAssignments_eq_permutations τ e k
    (fun n hn => he n (Finset.mem_union_left _ hn))
    (fun n hn => hk n (Finset.mem_union_left _ hn))
  have hc' := c.mapAssignments_eq_permutations τ e k
    (fun n hn => he n (Finset.mem_union_right _ hn))
    (fun n hn => hk n (Finset.mem_union_right _ hn))
  exact ⟨e,k,hb.trans ha',hc' ▸ hc⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
