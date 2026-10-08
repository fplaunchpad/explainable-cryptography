import ExplainableCrypto.Helios.Symbolic.SourceNamedPresentationNames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- New-Par, New-0 and Par-0 remove any restriction unused by its whole body. -/
theorem Structural.name_unused (a : Named V) (n : SourceName) (hf : n ∉ a.freeNames) :
    Structural (.newName n a) a :=
  (Structural.newName n (Structural.zero a).symm).trans
    ((Structural.namePar a n (.embed (.plain .nil)) hf).symm.trans
      ((Structural.parRight a (Structural.nameZero n)).trans (Structural.zero a)))

theorem freeNames_restrictNames (ns : List SourceName) (a : Named V) :
    (restrictNames ns a).freeNames = a.freeNames \ ns.toFinset := by
  induction ns with
  | nil => simp [restrictNames]
  | cons n ns ih =>
    simp only [restrictNames,List.foldr,freeNames] at *
    rw [ih]
    ext u
    simp [and_left_comm]

/-- Repeated occurrences in a name prefix do not introduce new free names. -/
theorem Structural.restrictNames_unused (ns : List SourceName) (a : Named V)
    (hf : ∀ n ∈ ns, n ∉ a.freeNames) : Structural (Named.restrictNames ns a) a := by
  induction ns with
  | nil => exact .refl _
  | cons n ns ih =>
    exact (Structural.newName n (ih (fun m hm => hf m (by simp [hm])))).trans
      (Structural.name_unused a n (hf n (by simp)))

/-- Duplicate name restrictions are removable because the inner binder already
removes that name from the body's free-name set. -/
theorem Structural.name_duplicate (a : Named V) (n : SourceName) :
    Structural (.newName n (.newName n a)) (.newName n a) :=
  Structural.name_unused (.newName n a) n (by simp [freeNames])

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
