import ExplainableCrypto.Helios.Symbolic.SourceFreshInterpretation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Extrusion across a whole prefix requires freshness for every binder. -/
theorem Structural.par_restrictNames_right (a b : Named V) (ns : List SourceName)
    (hf : ∀ n ∈ ns, n ∉ a.freeNames) :
    Structural (.par a (Named.restrictNames ns b)) (Named.restrictNames ns (.par a b)) := by
  induction ns with
  | nil => exact .refl _
  | cons n ns ih =>
    exact (Structural.namePar a n _ (hf n (by simp))).trans
      (.newName n (ih (fun m hm => hf m (by simp [hm]))))

theorem Structural.par_restrictNames_left (a b : Named V) (ns : List SourceName)
    (hf : ∀ n ∈ ns, n ∉ b.freeNames) :
    Structural (.par (Named.restrictNames ns a) b) (Named.restrictNames ns (.par a b)) :=
  (Structural.comm _ _).trans ((Structural.par_restrictNames_right b a ns hf).trans
    ((Structural.comm b a).restrictNames ns))

theorem Structural.var_restrictNames (a : Named (Option V)) (ns : List SourceName) :
    Structural (.newVar (Named.restrictNames ns a)) (Named.restrictNames ns (.newVar a)) := by
  induction ns with
  | nil => exact .refl _
  | cons n ns ih =>
    exact (Structural.nameVarComm n _).symm.trans (.newName n ih)

theorem restrictNames_append (ns ms : List SourceName) (a : Named V) :
    restrictNames (ns ++ ms) a = restrictNames ns (Named.restrictNames ms a) := by
  simp only [restrictNames,List.foldr_append]

/-- Freshening a prefix changes its entire body by the same two permutations. -/
theorem exists_fresh_extended_prefix (ns : List SourceName) (a : Extended V) (avoid : Finset SourceName) :
    ∃ (ns' : List SourceName) (e k : Nat ≃ Nat),
      Structural (Named.restrictNames ns (.embed a)) (Named.restrictNames ns' (.embed (a.mapNames e k))) ∧
      ∀ n ∈ ns', n ∉ avoid := by
  obtain ⟨ns',e,k,ha,_,hf,_⟩ := exists_common_fresh_prefix ns (.embed a) (.embed a) avoid
  exact ⟨ns',e,k,ha,hf⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
