import ExplainableCrypto.Helios.Symbolic.SourceNamedFrameProjection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type}

/-- All Extended structural rules descend to the full retained frame. -/
theorem Extended.Structural.frameOf {a b : Extended V} (h : Extended.Structural a b) :
    Extended.Structural a.frameOf b.frameOf := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newVar h ih => exact .newVar ih
  | plainPar => exact (Extended.Structural.zero _).symm
  | zero => exact .zero _
  | assoc => exact .assoc _ _ _
  | comm => exact .comm _ _
  | newPar a b =>
    simpa only [Extended.frameOf,Extended.frameOf_rename] using
      Extended.Structural.newPar a.frameOf b.frameOf
  | «alias» m => exact .alias m
  | substPlain => exact .refl _
  | substActive x y m n hxy => exact .substActive x y m n hxy
  | rewrite x h => exact .rewrite x h

/-- Alpha and extrusion remain legal after extraction because the retained
frame has no additional free names or nested binder names. -/
theorem Named.Structural.frameOf {a b : Named V} (h : Named.Structural a b) :
    Named.Structural a.frameOf b.frameOf := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | embed h => exact .embed h.frameOf
  | parLeft c h ih => exact .parLeft _ ih
  | parRight a h ih => exact .parRight _ ih
  | newName n h ih => exact .newName n ih
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
    simpa only [Named.frameOf,Named.frameOf_rename] using Named.Structural.varComm a.frameOf
  | namePar a n b hf => exact .namePar _ _ _ (fun hn => hf (a.frameOf_freeNames hn))
  | varPar a b =>
    simpa only [Named.frameOf,Named.frameOf_rename] using Named.Structural.varPar a.frameOf b.frameOf
  | alphaBase a n m hf =>
    simpa only [Named.frameOf,Named.frameOf_mapNames] using
      Named.Structural.alphaBase a.frameOf n m (fun hn => hf (a.frameOf_allNames hn))
  | alphaChannel a n m hf =>
    simpa only [Named.frameOf,Named.frameOf_mapNames] using
      Named.Structural.alphaChannel a.frameOf n m (fun hn => hf (a.frameOf_allNames hn))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
