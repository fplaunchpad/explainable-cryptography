import ExplainableCrypto.Helios.Symbolic.SourceFreshRepresentatives

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

theorem SourceName.map_comp (u : SourceName) (f g f' g' : Nat → Nat) :
    (u.map f g).map f' g' = u.map (f' ∘ f) (g' ∘ g) := by
  cases u <;> rfl

namespace Named

theorem mapNames_id (a : Named V) : a.mapNames id id = a := by
  induction a with
  | embed a => exact congrArg Named.embed (Extended.mapNames_id a)
  | par a b ha hb => simp only [mapNames,ha,hb]
  | newVar a ha => simp only [mapNames,ha]
  | newName n a ha => cases n <;> simp only [mapNames,SourceName.map,ha,id]

theorem mapNames_comp (a : Named V) (f g f' g' : Nat → Nat) :
    (a.mapNames f g).mapNames f' g' = a.mapNames (f' ∘ f) (g' ∘ g) := by
  induction a with
  | embed a => exact congrArg Named.embed (Extended.mapNames_comp a f g f' g')
  | par a b ha hb => simp only [mapNames,ha,hb]
  | newVar a ha => simp only [mapNames,ha]
  | newName n a ha => cases n <;> simp only [mapNames,SourceName.map,ha,Function.comp_def]

theorem mapNames_restrictNames (ns : List SourceName) (a : Named V) (f g : Nat → Nat) :
    (restrictNames ns a).mapNames f g = restrictNames (ns.map (SourceName.map f g)) (a.mapNames f g) := by
  induction ns <;> simp_all only [restrictNames,List.foldr,List.map,mapNames]

theorem mem_allNames_of_mem_restriction (ns : List SourceName) (a : Named V) (u : SourceName) (h : u ∈ ns) :
    u ∈ (restrictNames ns a).allNames := by
  induction ns with
  | nil => cases h
  | cons n ns ih =>
    rcases List.mem_cons.mp h with he | h
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert_of_mem (ih h)

theorem mapNames_restrict_base_swap (ns : List SourceName) (a : Named V) (n m : Nat)
    (hn : SourceName.base n ∉ ns) (hm : SourceName.base m ∉ ns) :
    (restrictNames ns a).mapNames (Equiv.swap n m) id = restrictNames ns (a.mapNames (Equiv.swap n m) id) := by
  rw [mapNames_restrictNames]
  have he : ns.map (SourceName.map (Equiv.swap n m) id) = ns := by
    calc
      ns.map (SourceName.map (Equiv.swap n m) id) = ns.map id := by
        apply List.map_congr_left
        intro u hu
        exact SourceName.base_swap_fixes u n m (fun h => hn (h ▸ hu)) (fun h => hm (h ▸ hu))
      _ = ns := List.map_id ns
  rw [he]

theorem mapNames_restrict_channel_swap (ns : List SourceName) (a : Named V) (n m : Nat)
    (hn : SourceName.channel n ∉ ns) (hm : SourceName.channel m ∉ ns) :
    (restrictNames ns a).mapNames id (Equiv.swap n m) = restrictNames ns (a.mapNames id (Equiv.swap n m)) := by
  rw [mapNames_restrictNames]
  have he : ns.map (SourceName.map id (Equiv.swap n m)) = ns := by
    calc
      ns.map (SourceName.map id (Equiv.swap n m)) = ns.map id := by
        apply List.map_congr_left
        intro u hu
        exact SourceName.channel_swap_fixes u n m (fun h => hn (h ▸ hu)) (fun h => hm (h ▸ hu))
      _ = ns := List.map_id ns
  rw [he]

theorem prefix_image_cons (ns ns' : List SourceName) (u v : SourceName) (ρ τ : SourceName → SourceName)
    (hi : ∀ w ∈ ns, ρ w ∈ ns') (hf : u ∉ ns → ρ u = u)
    (ht : ∀ w ∈ ns', τ w = w) (hu : τ u = v) :
    ∀ w ∈ u :: ns, τ (ρ w) ∈ v :: ns' := by
  intro w hw
  rcases List.mem_cons.mp hw with he | hw
  · subst w
    by_cases h : u ∈ ns
    · rw [ht _ (hi u h)]
      exact List.mem_cons_of_mem _ (hi u h)
    · rw [hf h,hu]
      exact List.mem_cons_self
  · rw [ht _ (hi w hw)]
    exact List.mem_cons_of_mem _ (hi w hw)

theorem prefix_fixes_avoid_cons (ns : List SourceName) (u : SourceName) (avoid : Finset SourceName)
    (ρ τ : SourceName → SourceName)
    (hf : ∀ w ∈ avoid, w ∉ ns → ρ w = w)
    (ht : ∀ w ∈ avoid, w ≠ u → τ w = w) :
    ∀ w ∈ avoid, w ∉ u :: ns → τ (ρ w) = w := by
  intro w hw hn
  have hns : w ∉ ns := fun h => hn (List.mem_cons_of_mem _ h)
  have hne : w ≠ u := fun h => hn (List.mem_cons.mpr (Or.inl h))
  rw [hf w hw hns,ht w hw hne]
end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
