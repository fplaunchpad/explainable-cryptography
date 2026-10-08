import ExplainableCrypto.Helios.Symbolic.SourceNamedElectionStatic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

theorem Formula.nameSupport_mapNames (a : Formula V) (f : Nat → Nat) :
    (a.mapNames f).nameSupport = a.nameSupport.image f := by
  induction a <;> simp_all only [Formula.mapNames,Formula.nameSupport,Term.nameSupport_mapNames,Finset.image_union]

theorem Agent.nameSupport_mapNames (a : Agent V) (f g : Nat → Nat) :
    (a.mapNames f g).nameSupport = a.nameSupport.image (SourceName.map f g) := by
  induction a <;> simp_all [Agent.mapNames,Agent.nameSupport,Term.nameSupport_mapNames,
    Formula.nameSupport_mapNames,Finset.image_union,Finset.image_image,Function.comp_def,SourceName.map]

theorem Extended.nameSupport_mapNames (a : Extended V) (f g : Nat → Nat) :
    (a.mapNames f g).nameSupport = a.nameSupport.image (SourceName.map f g) := by
  induction a <;> simp_all [Extended.mapNames,Extended.nameSupport,Agent.nameSupport_mapNames,
    Term.nameSupport_mapNames,Finset.image_union,Finset.image_image,Function.comp_def,SourceName.map]

theorem Extended.FreeLabel.nameSupport_mapNames (l : Extended.FreeLabel V) (f g : Nat → Nat) :
    (l.mapNames f g).nameSupport = l.nameSupport.image (SourceName.map f g) := by
  cases l <;> simp [Extended.FreeLabel.mapNames,Extended.FreeLabel.nameSupport,
    Term.nameSupport_mapNames,Finset.image_image,Function.comp_def,SourceName.map]

namespace Named

theorem allNames_mapNames (a : Named V) (f g : Nat → Nat) :
    (a.mapNames f g).allNames = a.allNames.image (SourceName.map f g) := by
  induction a <;> simp_all [Named.mapNames,allNames,Extended.nameSupport_mapNames,Finset.image_union]

theorem freeNames_mapNames (a : Named V) (e k : Nat ≃ Nat) :
    (a.mapNames e k).freeNames = a.freeNames.image (SourceName.map e k) := by
  induction a with
  | embed a => exact a.nameSupport_mapNames e k
  | par a b ha hb => simp only [Named.mapNames,freeNames,ha,hb,Finset.image_union]
  | newVar a ih => exact ih
  | newName n a ih =>
    simp only [Named.mapNames,freeNames,ih]
    exact (Finset.image_erase (SourceName.map_injective e k) a.freeNames n).symm

theorem mem_allNames_mapNames (a : Named V) (e k : Nat ≃ Nat) (n : SourceName) :
    n.map e k ∈ (a.mapNames e k).allNames ↔ n ∈ a.allNames := by
  rw [allNames_mapNames]
  constructor
  · rintro hn
    obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
    exact SourceName.map_injective e k he ▸ hm
  · exact fun h => Finset.mem_image.mpr ⟨n,h,rfl⟩

theorem mem_freeNames_mapNames (a : Named V) (e k : Nat ≃ Nat) (n : SourceName) :
    n.map e k ∈ (a.mapNames e k).freeNames ↔ n ∈ a.freeNames := by
  rw [freeNames_mapNames]
  constructor
  · rintro hn
    obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
    exact SourceName.map_injective e k he ▸ hm
  · exact fun h => Finset.mem_image.mpr ⟨n,h,rfl⟩

/-- A uniform permutation conjugates an alpha swap to the swap of its images. -/
theorem mapNames_base_swap (a : Named V) (e k : Nat ≃ Nat) (n m : Nat) :
    (a.mapNames (Equiv.swap n m) id).mapNames e k =
      (a.mapNames e k).mapNames (Equiv.swap (e n) (e m)) id := by
  simp only [mapNames_comp,Function.comp_id,Function.id_comp,e.injective.swap_comp]

theorem mapNames_channel_swap (a : Named V) (e k : Nat ≃ Nat) (n m : Nat) :
    (a.mapNames id (Equiv.swap n m)).mapNames e k =
      (a.mapNames e k).mapNames id (Equiv.swap (k n) (k m)) := by
  simp only [mapNames_comp,Function.comp_id,Function.id_comp,k.injective.swap_comp]

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
