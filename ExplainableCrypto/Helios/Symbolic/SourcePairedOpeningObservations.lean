import ExplainableCrypto.Helios.Symbolic.SourcePairedVisibleOpenings

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W : Type}

/-- Paired openings across variable domains retain finite faithfulness and the
literal assignment outside the restriction prefix, including observation names. -/
theorem Opens.prefix_faithful_pair_fixed (bound : List SourceName) (a : Extended V) (c : Extended W)
    (ρ : NameAssignment) {ns : List SourceName} {b : Extended V}
    (h : Opens (restrictNames bound (.embed a)) ρ ns b) (S : Finset SourceName)
    (hi : ρ.FaithfulOn S)
    (hf : ∀ n ∈ ns, n ∉ S.image (SourceName.map ρ.base ρ.channel)) :
    ∃ τ : NameAssignment, b = a.mapNames τ.base τ.channel ∧ τ.FaithfulOn S ∧
      Opens (restrictNames bound (.embed c)) ρ ns (c.mapNames τ.base τ.channel) ∧
      ∀ n, n ∉ bound → τ n = ρ n := by
  induction bound generalizing ρ ns with
  | nil => cases h; exact ⟨ρ,rfl,hi,.embed c ρ,fun _ _ => rfl⟩
  | cons n bound ih =>
    cases h with
    | newName _ v h hn =>
      obtain ⟨τ,hb,ht,hc,hfix⟩ := ih (Function.update ρ n v) h
        (hi.update_fresh n v (hf _ List.mem_cons_self))
        (fun m hm => nameAssignment_fresh_update_image ρ S n v m
          (hf m (List.mem_cons_of_mem _ hm)) (fun he => hn (he ▸ hm)))
      refine ⟨τ,hb,ht,.newName n v hc hn,?_⟩
      intro m hm
      have hmn : m ≠ n := fun he => hm (he ▸ List.mem_cons_self)
      rw [hfix m (fun hh => hm (List.mem_cons_of_mem _ hh)),Function.update_of_ne hmn]

/-- One pair of permutations describes both endpoints and fixes every supplied
observation name outside the original restriction prefix. -/
theorem Opens.prefix_permutations_fixed_pair (bound : List SourceName) (a : Extended V) (c : Extended W)
    {ns : List SourceName} {b : Extended V}
    (h : Opens (restrictNames bound (.embed a)) NameAssignment.literal ns b)
    (S : Finset SourceName) (ha : a.nameSupport ⊆ S) (hc : c.nameSupport ⊆ S)
    (hf : ∀ n ∈ ns, n ∉ S) :
    ∃ e k : Nat ≃ Nat, b = a.mapNames e k ∧
      Opens (restrictNames bound (.embed c)) NameAssignment.literal ns (c.mapNames e k) ∧
      ∀ n ∈ S, n ∉ bound → n.map e k = n := by
  have hmap : SourceName.map NameAssignment.literal.base NameAssignment.literal.channel = id := by
    funext n; cases n <;> rfl
  have hi : NameAssignment.literal.FaithfulOn S := by
    intro x y hx hy he
    simpa only [hmap,id_eq] using he
  obtain ⟨τ,hb,ht,hc',hfix⟩ := h.prefix_faithful_pair_fixed bound a c NameAssignment.literal S hi
    (by simpa only [hmap,Finset.image_id] using hf)
  obtain ⟨e,k,he,hk⟩ := ht.exists_permutations
  have ha' := a.mapAssignments_eq_permutations τ e k (fun n hn => he n (ha hn)) (fun n hn => hk n (ha hn))
  have ht' := c.mapAssignments_eq_permutations τ e k (fun n hn => he n (hc hn)) (fun n hn => hk n (hc hn))
  refine ⟨e,k,hb.trans ha',ht' ▸ hc',?_⟩
  intro n hn hnb
  have hh := hfix n hnb
  cases n with
  | base n => exact congrArg SourceName.base ((he n hn).trans hh)
  | channel n => exact congrArg SourceName.channel ((hk n hn).trans hh)

/-- The entire input recipe, including all four SPK fields, stays fixed when
all names in its full label support stay fixed. -/
theorem input_label_fixed {c : Nat} {r : Recipe handles} {e k : Nat ≃ Nat}
    (h : ∀ n ∈ (Extended.FreeLabel.input c r).nameSupport, n.map e k = n) :
    k c = c ∧ r.mapNames e = r := by
  constructor
  · exact SourceName.channel.inj (h (.channel c) (by simp [Extended.FreeLabel.nameSupport]))
  · have he : r.mapNames e = r.mapNames id := by
      apply r.mapNames_congr
      intro n hn
      exact SourceName.base.inj (h (.base n) (by simp [Extended.FreeLabel.nameSupport,hn]))
    exact he.trans r.mapNames_id

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
