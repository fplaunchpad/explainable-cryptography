import ExplainableCrypto.Helios.Symbolic.SourceChannelSupport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

/-- Base restrictions do not bind channels. Channel restrictions remove their
own channel from the free support, including through nested contexts. -/
def channels : {V : Type} → Named V → Finset Nat
  | _, .embed a => a.channels
  | _, .par a b => a.channels ∪ b.channels
  | _, .newName (.base _) a => a.channels
  | _, .newName (.channel c) a => a.channels.erase c
  | _, .newVar a => a.channels

theorem channel_mem_freeNames (a : Named V) (c : Nat) :
    c ∈ a.channels ↔ SourceName.channel c ∈ a.freeNames := by
  induction a with
  | embed a => exact Extended.channel_mem_nameSupport a c
  | par a b ha hb => simp only [channels,freeNames,Finset.mem_union,ha,hb]
  | newVar a ha => exact ha
  | newName n a ha => cases n <;> simp_all [channels,freeNames]

theorem freeNames_subset_allNames (a : Named V) : a.freeNames ⊆ a.allNames := by
  induction a with
  | embed a => exact Finset.Subset.refl _
  | par a b ha hb => exact Finset.union_subset_union ha hb
  | newVar a ha => exact ha
  | newName n a ha =>
    intro m hm
    exact Finset.mem_insert_of_mem (ha (Finset.mem_of_mem_erase hm))

theorem channels_rename (a : Named V) (σ : V → W) : (a.rename σ).channels = a.channels := by
  induction a generalizing W with
  | embed a => exact Extended.channels_rename a σ
  | par a b ha hb => simp only [rename,channels,ha,hb]
  | newVar a ha => exact ha _
  | newName n a ha => cases n <;> simp only [rename,channels,ha]

theorem channels_mapNames (a : Named V) (f : Nat → Nat) (k : Nat ≃ Nat) :
    (a.mapNames f k).channels = a.channels.image k := by
  induction a with
  | embed a => exact Extended.channels_mapNames a f k
  | par a b ha hb => simp only [mapNames,channels,ha,hb,Finset.image_union]
  | newVar a ha => exact ha
  | newName n a ha =>
    cases n with
    | base n => exact ha
    | channel n =>
      simp only [mapNames,SourceName.map,channels,ha]
      exact (Finset.image_erase k.injective a.channels n).symm

theorem channels_mapBaseNames (a : Named V) (f : Nat → Nat) :
    (a.mapNames f id).channels = a.channels := by
  simpa using channels_mapNames a f (Equiv.refl Nat)

/-- A fresh same-sort alpha swap preserves free channels after replacing the
old binder by the new one. Freshness is essential for this statement. -/
theorem swap_erase_fresh (s : Finset Nat) (n m : Nat) (hf : m ∉ s) :
    (s.image (Equiv.swap n m)).erase m = s.erase n := by
  ext c
  simp only [Finset.mem_erase,Finset.mem_image]
  constructor
  · rintro ⟨hcm,x,hx,rfl⟩
    have hxn : x ≠ n := by intro he; subst x; exact hcm (by simp)
    have hxm : x ≠ m := by intro he; subst x; exact hf hx
    have he : Equiv.swap n m x = x := by simp [Equiv.swap_apply_def,hxn,hxm]
    rw [he]
    exact ⟨hxn,hx⟩
  · rintro ⟨hcn,hc⟩
    have hcm : c ≠ m := by intro he; subst c; exact hf hc
    refine ⟨hcm,c,hc,?_⟩
    simp [Equiv.swap_apply_def,hcn,hcm]

/-- Covers every structural derivation, including alpha conversion, extrusion,
active substitution, and full E rewriting of base-message payloads. -/
theorem Structural.channels {a b : Named V} (h : Structural a b) : a.channels = b.channels := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | embed h => exact h.channels
  | parLeft c h ih => simp only [Named.channels,ih]
  | parRight a h ih => simp only [Named.channels,ih]
  | newName n h ih => cases n <;> simp only [Named.channels,ih]
  | newVar h ih => exact ih
  | embedPar => rfl
  | embedVar => rfl
  | zero => simp [Named.channels,Extended.channels,Agent.channels]
  | assoc => exact Finset.union_assoc _ _ _
  | comm => exact Finset.union_comm _ _
  | nameZero n => cases n <;> rfl
  | nameComm n m a =>
    cases n <;> cases m <;> simp only [Named.channels]
    ext c
    simp [and_left_comm]
  | nameVarComm n a => cases n <;> rfl
  | varComm a => exact (channels_rename a _).symm
  | namePar a n b hf =>
    cases n with
    | base n => rfl
    | channel c =>
      have hc : c ∉ a.channels := fun h => hf ((channel_mem_freeNames a c).mp h)
      ext d
      simp only [Named.channels,Finset.mem_union,Finset.mem_erase]
      constructor
      · rintro (ha | ⟨hd,hb⟩)
        · exact ⟨fun he => hc (he ▸ ha),Or.inl ha⟩
        · exact ⟨hd,Or.inr hb⟩
      · rintro ⟨hd,ha | hb⟩
        · exact Or.inl ha
        · exact Or.inr ⟨hd,hb⟩
  | varPar a b => simp only [Named.channels,channels_rename]
  | alphaBase a n m hf => exact (channels_mapBaseNames a _).symm
  | alphaChannel a n m hf =>
    have hm : m ∉ a.channels := fun h => hf (freeNames_subset_allNames a ((channel_mem_freeNames a m).mp h))
    simp only [Named.channels,channels_mapNames]
    exact (swap_erase_fresh a.channels n m hm).symm
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
