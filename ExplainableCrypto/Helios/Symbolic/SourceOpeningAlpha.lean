import ExplainableCrypto.Helios.Symbolic.SourceOpeningSupport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

def NameAssignment.permutations (e k : Nat ≃ Nat) : NameAssignment
  | .base n => e n
  | .channel n => k n

theorem SourceName.map_permutations (n : SourceName) (e k : Nat ≃ Nat) :
    n.map (NameAssignment.permutations e k).base (NameAssignment.permutations e k).channel = n.map e k := rfl

theorem fresh_image_swap {S : Finset SourceName} {old fresh m : SourceName}
    (hm : m ∉ insert old S) (hf : m ≠ fresh) : m ∉ S.image (Equiv.swap old fresh) := by
  rintro h
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp h
  have ho : m ≠ old := fun he => hm (he ▸ Finset.mem_insert_self old S)
  have hfix := Equiv.swap_apply_of_ne_of_ne ho hf
  have hxm : x=m := (Equiv.swap old fresh).injective (he.trans hfix.symm)
  exact hm (Finset.mem_insert_of_mem (hxm ▸ hx))

namespace Named
variable {V : Type}

theorem opening_alphaBase_agreement (a : Named V) (ρ : NameAssignment)
    (e k : Nat ≃ Nat) (n v : Nat)
    (he : ∀ m ∈ (Named.newName (.base n) a).freeNames, ρ m = NameAssignment.permutations e k m)
    (hf : SourceName.base v ∉ (a.mapNames e k).allNames) :
    ∀ m ∈ a.freeNames,
      Function.update ρ (.base n) v m = NameAssignment.permutations (e.trans (Equiv.swap (e n) v)) k m := by
  intro m hm
  cases m with
  | channel c =>
    simpa [NameAssignment.permutations] using he (.channel c) (Finset.mem_erase.mpr ⟨by simp,hm⟩)
  | base m =>
    by_cases hn : m=n
    · subst m
      simp [NameAssignment.permutations]
    · have hmv : e m ≠ v := by
        intro h
        apply hf
        rw [allNames_mapNames]
        exact Finset.mem_image.mpr ⟨.base m,freeNames_subset_allNames a hm,by simp [SourceName.map,h]⟩
      have he' := he (.base m) (Finset.mem_erase.mpr ⟨by simpa using hn,hm⟩)
      simpa [NameAssignment.permutations,Equiv.swap_apply_of_ne_of_ne (e.injective.ne hn) hmv,hn] using he'

theorem opening_alphaChannel_agreement (a : Named V) (ρ : NameAssignment)
    (e k : Nat ≃ Nat) (n v : Nat)
    (he : ∀ m ∈ (Named.newName (.channel n) a).freeNames, ρ m = NameAssignment.permutations e k m)
    (hf : SourceName.channel v ∉ (a.mapNames e k).allNames) :
    ∀ m ∈ a.freeNames,
      Function.update ρ (.channel n) v m = NameAssignment.permutations e (k.trans (Equiv.swap (k n) v)) m := by
  intro m hm
  cases m with
  | base c =>
    simpa [NameAssignment.permutations] using he (.base c) (Finset.mem_erase.mpr ⟨by simp,hm⟩)
  | channel m =>
    by_cases hn : m=n
    · subst m
      simp [NameAssignment.permutations]
    · have hmv : k m ≠ v := by
        intro h
        apply hf
        rw [allNames_mapNames]
        exact Finset.mem_image.mpr ⟨.channel m,freeNames_subset_allNames a hm,by simp [SourceName.map,h]⟩
      have he' := he (.channel m) (Finset.mem_erase.mpr ⟨by simpa using hn,hm⟩)
      simpa [NameAssignment.permutations,Equiv.swap_apply_of_ne_of_ne (k.injective.ne hn) hmv,hn] using he'

theorem opening_alphaBase_fresh (a : Named V) (e k : Nat ≃ Nat) (n v : Nat)
    (m : SourceName) (hm : m ∉ insert (.base (e n)) (a.mapNames e k).allNames)
    (hv : m ≠ .base v) : m ∉ (a.mapNames (e.trans (Equiv.swap (e n) v)) k).allNames := by
  have hs := fresh_image_swap hm hv
  rw [← SourceName.map_base_swap_eq (e n) v,← allNames_mapNames] at hs
  simpa only [Named.mapNames_comp,Function.id_comp,Equiv.coe_trans] using hs

theorem opening_alphaChannel_fresh (a : Named V) (e k : Nat ≃ Nat) (n v : Nat)
    (m : SourceName) (hm : m ∉ insert (.channel (k n)) (a.mapNames e k).allNames)
    (hv : m ≠ .channel v) : m ∉ (a.mapNames e (k.trans (Equiv.swap (k n) v))).allNames := by
  have hs := fresh_image_swap hm hv
  rw [← SourceName.map_channel_swap_eq (k n) v,← allNames_mapNames] at hs
  simpa only [Named.mapNames_comp,Function.id_comp,Equiv.coe_trans] using hs

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
