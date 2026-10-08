import ExplainableCrypto.Helios.Symbolic.SourceNamedNameSupport

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- All Named structural paths transport under independent name permutations,
including alpha conversions inside arbitrary evaluation contexts. -/
theorem Structural.mapNames {a b : Named V} (h : Structural a b) (e k : Nat ≃ Nat) :
    Structural (a.mapNames e k) (b.mapNames e k) := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | embed h => exact .embed (h.mapNames e k)
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newName n h ih => exact .newName (n.map e k) ih
  | newVar h ih => exact .newVar ih
  | embedPar => exact .embedPar _ _
  | embedVar => exact .embedVar _
  | zero => exact .zero _
  | assoc => exact .assoc _ _ _
  | comm => exact .comm _ _
  | nameZero => exact .nameZero _
  | nameComm => exact .nameComm _ _ _
  | nameVarComm => exact .nameVarComm _ _
  | varComm a =>
    simpa only [Named.mapNames,mapNames_rename] using Structural.varComm (a.mapNames e k)
  | namePar a n b hf => exact .namePar _ _ _ (fun h => hf ((mem_freeNames_mapNames a e k n).mp h))
  | varPar a b =>
    simpa only [Named.mapNames,mapNames_rename] using Structural.varPar (a.mapNames e k) (b.mapNames e k)
  | alphaBase a n m hf =>
    simpa only [Named.mapNames,SourceName.map,mapNames_base_swap] using
      Structural.alphaBase (a.mapNames e k) (e n) (e m)
        (fun h => hf ((mem_allNames_mapNames a e k (.base m)).mp h))
  | alphaChannel a n m hf =>
    simpa only [Named.mapNames,SourceName.map,mapNames_channel_swap] using
      Structural.alphaChannel (a.mapNames e k) (k n) (k m)
        (fun h => hf ((mem_allNames_mapNames a e k (.channel m)).mp h))

theorem Structural.mapNames_iff (a b : Named V) (e k : Nat ≃ Nat) :
    Structural (a.mapNames e k) (b.mapNames e k) ↔ Structural a b := by
  constructor
  · intro h
    simpa only [Named.mapNames_inverse] using h.mapNames e.symm k.symm
  · exact fun h => h.mapNames e k

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
