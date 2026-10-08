import ExplainableCrypto.Helios.Symbolic.SourceNamedNameStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

theorem Extended.FreeLabel.mem_nameSupport_mapNames (l : Extended.FreeLabel V)
    (e k : Nat ≃ Nat) (n : SourceName) : n.map e k ∈ (l.mapNames e k).nameSupport ↔ n ∈ l.nameSupport := by
  rw [Extended.FreeLabel.nameSupport_mapNames]
  constructor
  · intro hn
    obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
    exact SourceName.map_injective e k he ▸ hm
  · exact fun h => Finset.mem_image.mpr ⟨n,h,rfl⟩

namespace Named

theorem Reduction.mapNames {a b : Named V} (h : Reduction a b) (e k : Nat ≃ Nat) :
    Reduction (a.mapNames e k) (b.mapNames e k) := by
  induction h with
  | embed h => exact .embed (h.mapNames e k)
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newName n h ih => exact .newName (n.map e k) ih
  | newVar h ih => exact .newVar ih
  | congr ha h hb ih => exact .congr (ha.mapNames e k) ih (hb.mapNames e k)

theorem Reduction.mapNames_iff (a b : Named V) (e k : Nat ≃ Nat) :
    Reduction (a.mapNames e k) (b.mapNames e k) ↔ Reduction a b := by
  constructor
  · intro h
    simpa only [Named.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

theorem FreeStep.mapNames {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) (e k : Nat ≃ Nat) :
    FreeStep (a.mapNames e k) (l.mapNames e k) (b.mapNames e k) := by
  induction h with
  | embed h => exact .embed (h.mapNames e k)
  | scopeName n hf h ih =>
    exact .scopeName (n.map e k) (fun hn => hf ((Extended.FreeLabel.mem_nameSupport_mapNames _ e k n).mp hn)) ih
  | scopeInput h ih =>
    apply FreeStep.scopeInput
    simpa only [Extended.FreeLabel.mapNames,shiftTerm_mapNames] using ih
  | scopeOutput h ih => exact .scopeOutput ih
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | congr ha h hb ih => exact .congr (ha.mapNames e k) ih (hb.mapNames e k)

theorem FreeStep.mapNames_iff (a b : Named V) (l : Extended.FreeLabel V) (e k : Nat ≃ Nat) :
    FreeStep (a.mapNames e k) (l.mapNames e k) (b.mapNames e k) ↔ FreeStep a l b := by
  constructor
  · intro h
    simpa only [Named.mapNames_inverse,Extended.FreeLabel.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

theorem BoundOutput.mapNames {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (e k : Nat ≃ Nat) : BoundOutput (a.mapNames e k) (k c) (b.mapNames e k) := by
  induction h with
  | embed h => exact .embed (h.mapNames e k)
  | openAtom h => exact .openAtom (h.mapNames e k)
  | scopeName n hf h ih => exact .scopeName (n.map e k) (fun hn => hf (SourceName.map_injective e k hn)) ih
  | scopeVar h ih =>
    simpa only [Named.mapNames,mapNames_rename] using BoundOutput.scopeVar ih
  | parLeft d h ih =>
    simpa only [Named.mapNames,mapNames_rename] using BoundOutput.parLeft (d.mapNames e k) ih
  | parRight a h ih =>
    simpa only [Named.mapNames,mapNames_rename] using BoundOutput.parRight (a.mapNames e k) ih
  | congr ha h hb ih => exact .congr (ha.mapNames e k) ih (hb.mapNames e k)

theorem BoundOutput.mapNames_iff (a : Named V) (b : Named (Option V)) (c : Nat) (e k : Nat ≃ Nat) :
    BoundOutput (a.mapNames e k) (k c) (b.mapNames e k) ↔ BoundOutput a c b := by
  constructor
  · intro h
    simpa only [Named.mapNames_inverse,Equiv.symm_apply_apply] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

theorem internal_star_mapNames {a b : Named V} (h : Relation.ReflTransGen Reduction a b) (e k : Nat ≃ Nat) :
    Relation.ReflTransGen Reduction (a.mapNames e k) (b.mapNames e k) := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (hstep.mapNames e k)

theorem internal_star_mapNames_iff (a b : Named V) (e k : Nat ≃ Nat) :
    Relation.ReflTransGen Reduction (a.mapNames e k) (b.mapNames e k) ↔ Relation.ReflTransGen Reduction a b := by
  constructor
  · intro h
    simpa only [Named.mapNames_inverse] using internal_star_mapNames h e.symm k.symm
  · exact fun h => internal_star_mapNames h e k

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
