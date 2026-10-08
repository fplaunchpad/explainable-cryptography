import ExplainableCrypto.Helios.Symbolic.SourceNamedNameActions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {hidden restricted : Finset Nat} {handles : Nat}

/-- Canonical prefix order may change under a permutation. Existing New-C
rules reorder it while all active values follow the same base-name map. -/
theorem canonicalFrame_mapNames (φ : Frame restricted handles) (e k : Nat ≃ Nat) :
    Structural ((canonicalFrame hidden φ).mapNames e k)
      (canonicalFrame (hidden.image k) (φ.mapNames e)) := by
  have hp : ((restrictionNames hidden restricted).map (SourceName.map e k)).Perm
      (restrictionNames (hidden.image k) (restricted.image e)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact (List.nodup_map_iff (fun _ _ h => SourceName.map_injective e k h)).mpr (restrictionNames_nodup _ _)
    · exact restrictionNames_nodup _ _
    · rw [← restrictionNames_image hidden restricted e k]
      ext n
      simp
  simpa only [canonicalFrame,mapNames_restrictNames,Named.mapNames,Extended.activeFrame_mapNames] using
    Structural.restrictNames_perm _ _ hp (.embed (Extended.activeFrame (φ.mapNames e)))

theorem RepresentsFrame.mapNames {a : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) (e k : Nat ≃ Nat) :
    (a.mapNames e k).RepresentsFrame (hidden.image k) (φ.mapNames e) := by
  have hs := Structural.mapNames h e k
  rw [← Named.frameOf_mapNames] at hs
  exact hs.trans (canonicalFrame_mapNames φ e k)

theorem representsFrame_mapNames_iff (a : Named (Fin handles)) (φ : Frame restricted handles) (e k : Nat ≃ Nat) :
    (a.mapNames e k).RepresentsFrame (hidden.image k) (φ.mapNames e) ↔ a.RepresentsFrame hidden φ := by
  cases φ
  constructor
  · intro h
    simpa only [RepresentsFrame,canonicalFrame,Extended.activeFrame,Named.mapNames_inverse,
      names_image_inverse,Frame.mapNames,Term.mapNames_inverse] using
      RepresentsFrame.mapNames h e.symm k.symm
  · exact fun h => h.mapNames e k

theorem StaticEq.mapNames {a b : Named (Fin handles)} (h : StaticEq a b) (e k : Nat ≃ Nat) :
    StaticEq (a.mapNames e k) (b.mapNames e k) := by
  obtain ⟨hidden,restricted,φ,ψ,ha,hb,he⟩ := h
  exact .of_presentations (ha.mapNames e k) (hb.mapNames e k) (he.mapNames e)

theorem staticEq_mapNames_iff (a b : Named (Fin handles)) (e k : Nat ≃ Nat) :
    StaticEq (a.mapNames e k) (b.mapNames e k) ↔ StaticEq a b := by
  constructor
  · intro h
    simpa only [Named.mapNames_inverse] using StaticEq.mapNames h e.symm k.symm
  · exact fun h => h.mapNames e k

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
