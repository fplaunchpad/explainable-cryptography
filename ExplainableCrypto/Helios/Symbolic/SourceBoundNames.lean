import ExplainableCrypto.Helios.Symbolic.SourceChannelPreservation
import Mathlib.Data.Finset.Lattice.Fold

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

def SourceName.index : SourceName → Nat
  | .base n | .channel n => n

/-- A concrete index outside either name sort in the finite set. -/
def freshNameIndex (s : Finset SourceName) : Nat := s.sup SourceName.index + 1

theorem fresh_base_not_mem (s : Finset SourceName) : SourceName.base (freshNameIndex s) ∉ s := by
  intro h
  have hl := Finset.le_sup (f := SourceName.index) h
  change s.sup SourceName.index + 1 ≤ s.sup SourceName.index at hl
  omega

theorem fresh_channel_not_mem (s : Finset SourceName) : SourceName.channel (freshNameIndex s) ∉ s := by
  intro h
  have hl := Finset.le_sup (f := SourceName.index) h
  change s.sup SourceName.index + 1 ≤ s.sup SourceName.index at hl
  omega

theorem SourceName.base_swap_fixes (u : SourceName) (n m : Nat)
    (hn : u ≠ .base n) (hm : u ≠ .base m) : u.map (Equiv.swap n m) id = u := by
  cases u <;> simp_all [SourceName.map,Equiv.swap_apply_def]

theorem SourceName.channel_swap_fixes (u : SourceName) (n m : Nat)
    (hn : u ≠ .channel n) (hm : u ≠ .channel m) : u.map id (Equiv.swap n m) = u := by
  cases u <;> simp_all [SourceName.map,Equiv.swap_apply_def]

namespace Named

def boundNames : {V : Type} → Named V → Finset SourceName
  | _, .embed _ => ∅
  | _, .par a b => a.boundNames ∪ b.boundNames
  | _, .newName n a => insert n a.boundNames
  | _, .newVar a => a.boundNames

theorem boundNames_subset_allNames (a : Named V) : a.boundNames ⊆ a.allNames := by
  induction a with
  | embed a => exact Finset.empty_subset _
  | par a b ha hb => exact Finset.union_subset_union ha hb
  | newName n a ha => exact Finset.insert_subset_insert n ha
  | newVar a ha => exact ha

theorem boundNames_mapNames (a : Named V) (f g : Nat → Nat) :
    (a.mapNames f g).boundNames = a.boundNames.image (SourceName.map f g) := by
  induction a <;> simp_all [boundNames,mapNames,Finset.image_union]

theorem boundNames_rename (a : Named V) (σ : V → W) : (a.rename σ).boundNames = a.boundNames := by
  induction a generalizing W <;> simp_all only [rename,boundNames]

/-- No inner binder moves when both swapped base names are absent there. -/
theorem boundNames_base_swap (a : Named V) (n m : Nat)
    (hn : SourceName.base n ∉ a.boundNames) (hm : SourceName.base m ∉ a.boundNames) :
    (a.mapNames (Equiv.swap n m) id).boundNames = a.boundNames := by
  rw [boundNames_mapNames]
  have he : a.boundNames.image (SourceName.map (Equiv.swap n m) id) = a.boundNames.image id := by
    apply Finset.image_congr
    intro u hu
    exact SourceName.base_swap_fixes u n m (fun h => hn (h ▸ hu)) (fun h => hm (h ▸ hu))
  simpa using he

theorem boundNames_channel_swap (a : Named V) (n m : Nat)
    (hn : SourceName.channel n ∉ a.boundNames) (hm : SourceName.channel m ∉ a.boundNames) :
    (a.mapNames id (Equiv.swap n m)).boundNames = a.boundNames := by
  rw [boundNames_mapNames]
  have he : a.boundNames.image (SourceName.map id (Equiv.swap n m)) = a.boundNames.image id := by
    apply Finset.image_congr
    intro u hu
    exact SourceName.channel_swap_fixes u n m (fun h => hn (h ▸ hu)) (fun h => hm (h ▸ hu))
  simpa using he
end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
